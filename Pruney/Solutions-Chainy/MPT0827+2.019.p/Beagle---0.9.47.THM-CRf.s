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
% DateTime   : Thu Dec  3 10:07:17 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 105 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 ( 194 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_232,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_241,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_232])).

tff(c_112,plain,(
    ! [A_38,B_39,C_40] :
      ( k1_relset_1(A_38,B_39,C_40) = k1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_121,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_112])).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_67,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_122,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_67])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_62,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_56])).

tff(c_66,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_62])).

tff(c_24,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    ! [A_28,B_29] :
      ( v1_relat_1(A_28)
      | ~ v1_relat_1(B_29)
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_74,plain,
    ( v1_relat_1(k6_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_68])).

tff(c_80,plain,(
    v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_74])).

tff(c_14,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_133,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(k1_relat_1(A_44),k1_relat_1(B_45))
      | ~ r1_tarski(A_44,B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_192,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,k1_relat_1(B_53))
      | ~ r1_tarski(k6_relat_1(A_52),B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(k6_relat_1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_133])).

tff(c_195,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_192])).

tff(c_198,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66,c_195])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_198])).

tff(c_201,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_242,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_201])).

tff(c_203,plain,(
    ! [A_54,B_55] :
      ( v1_relat_1(A_54)
      | ~ v1_relat_1(B_55)
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_212,plain,
    ( v1_relat_1(k6_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_203])).

tff(c_219,plain,(
    v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_212])).

tff(c_16,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_253,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k2_relat_1(A_64),k2_relat_1(B_65))
      | ~ r1_tarski(A_64,B_65)
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_333,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,k2_relat_1(B_79))
      | ~ r1_tarski(k6_relat_1(A_78),B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(k6_relat_1(A_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_253])).

tff(c_336,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_333])).

tff(c_339,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_66,c_336])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.31  
% 2.11/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.31  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.11/1.31  
% 2.11/1.31  %Foreground sorts:
% 2.11/1.31  
% 2.11/1.31  
% 2.11/1.31  %Background operators:
% 2.11/1.31  
% 2.11/1.31  
% 2.11/1.31  %Foreground operators:
% 2.11/1.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.11/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.11/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.11/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.31  
% 2.43/1.32  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 2.43/1.32  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.43/1.32  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.43/1.32  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.43/1.32  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.43/1.32  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.43/1.32  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.43/1.32  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.43/1.32  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.43/1.32  tff(c_232, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.32  tff(c_241, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_232])).
% 2.43/1.32  tff(c_112, plain, (![A_38, B_39, C_40]: (k1_relset_1(A_38, B_39, C_40)=k1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.43/1.32  tff(c_121, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_112])).
% 2.43/1.32  tff(c_22, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.43/1.32  tff(c_67, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_22])).
% 2.43/1.32  tff(c_122, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_67])).
% 2.43/1.32  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.43/1.32  tff(c_56, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.43/1.32  tff(c_62, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_56])).
% 2.43/1.32  tff(c_66, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_62])).
% 2.43/1.32  tff(c_24, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.43/1.32  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.32  tff(c_68, plain, (![A_28, B_29]: (v1_relat_1(A_28) | ~v1_relat_1(B_29) | ~r1_tarski(A_28, B_29))), inference(resolution, [status(thm)], [c_4, c_56])).
% 2.43/1.32  tff(c_74, plain, (v1_relat_1(k6_relat_1('#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_68])).
% 2.43/1.32  tff(c_80, plain, (v1_relat_1(k6_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_74])).
% 2.43/1.32  tff(c_14, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.32  tff(c_133, plain, (![A_44, B_45]: (r1_tarski(k1_relat_1(A_44), k1_relat_1(B_45)) | ~r1_tarski(A_44, B_45) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.43/1.32  tff(c_192, plain, (![A_52, B_53]: (r1_tarski(A_52, k1_relat_1(B_53)) | ~r1_tarski(k6_relat_1(A_52), B_53) | ~v1_relat_1(B_53) | ~v1_relat_1(k6_relat_1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_133])).
% 2.43/1.32  tff(c_195, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k6_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_192])).
% 2.43/1.32  tff(c_198, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66, c_195])).
% 2.43/1.32  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_198])).
% 2.43/1.32  tff(c_201, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_22])).
% 2.43/1.32  tff(c_242, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_201])).
% 2.43/1.32  tff(c_203, plain, (![A_54, B_55]: (v1_relat_1(A_54) | ~v1_relat_1(B_55) | ~r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_4, c_56])).
% 2.43/1.32  tff(c_212, plain, (v1_relat_1(k6_relat_1('#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_203])).
% 2.43/1.32  tff(c_219, plain, (v1_relat_1(k6_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_212])).
% 2.43/1.32  tff(c_16, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.32  tff(c_253, plain, (![A_64, B_65]: (r1_tarski(k2_relat_1(A_64), k2_relat_1(B_65)) | ~r1_tarski(A_64, B_65) | ~v1_relat_1(B_65) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.43/1.32  tff(c_333, plain, (![A_78, B_79]: (r1_tarski(A_78, k2_relat_1(B_79)) | ~r1_tarski(k6_relat_1(A_78), B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(k6_relat_1(A_78)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_253])).
% 2.43/1.32  tff(c_336, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k6_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_333])).
% 2.43/1.32  tff(c_339, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_66, c_336])).
% 2.43/1.32  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_242, c_339])).
% 2.43/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.32  
% 2.43/1.32  Inference rules
% 2.43/1.32  ----------------------
% 2.43/1.32  #Ref     : 0
% 2.43/1.32  #Sup     : 67
% 2.43/1.32  #Fact    : 0
% 2.43/1.32  #Define  : 0
% 2.43/1.32  #Split   : 3
% 2.43/1.32  #Chain   : 0
% 2.43/1.32  #Close   : 0
% 2.43/1.32  
% 2.43/1.32  Ordering : KBO
% 2.43/1.32  
% 2.43/1.32  Simplification rules
% 2.43/1.32  ----------------------
% 2.43/1.32  #Subsume      : 1
% 2.43/1.32  #Demod        : 24
% 2.43/1.32  #Tautology    : 20
% 2.43/1.33  #SimpNegUnit  : 2
% 2.43/1.33  #BackRed      : 4
% 2.43/1.33  
% 2.43/1.33  #Partial instantiations: 0
% 2.43/1.33  #Strategies tried      : 1
% 2.43/1.33  
% 2.43/1.33  Timing (in seconds)
% 2.43/1.33  ----------------------
% 2.43/1.33  Preprocessing        : 0.29
% 2.43/1.33  Parsing              : 0.15
% 2.43/1.33  CNF conversion       : 0.02
% 2.43/1.33  Main loop            : 0.23
% 2.43/1.33  Inferencing          : 0.09
% 2.43/1.33  Reduction            : 0.07
% 2.43/1.33  Demodulation         : 0.05
% 2.43/1.33  BG Simplification    : 0.01
% 2.43/1.33  Subsumption          : 0.03
% 2.43/1.33  Abstraction          : 0.01
% 2.43/1.33  MUC search           : 0.00
% 2.43/1.33  Cooper               : 0.00
% 2.43/1.33  Total                : 0.55
% 2.43/1.33  Index Insertion      : 0.00
% 2.43/1.33  Index Deletion       : 0.00
% 2.43/1.33  Index Matching       : 0.00
% 2.43/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
