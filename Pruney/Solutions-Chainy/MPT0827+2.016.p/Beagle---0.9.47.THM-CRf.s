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
% DateTime   : Thu Dec  3 10:07:16 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   55 (  77 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   74 ( 128 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_36,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_34,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_89,plain,(
    ! [A_35,B_36,C_37] :
      ( k2_relset_1(A_35,B_36,C_37) = k2_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_89])).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_45,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_45])).

tff(c_51,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_48])).

tff(c_22,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k1_relat_1(A_24),k1_relat_1(B_25))
      | ~ r1_tarski(A_24,B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_55,plain,(
    ! [A_10,B_25] :
      ( r1_tarski(A_10,k1_relat_1(B_25))
      | ~ r1_tarski(k6_relat_1(A_10),B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_52])).

tff(c_71,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,k1_relat_1(B_31))
      | ~ r1_tarski(k6_relat_1(A_30),B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_55])).

tff(c_74,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_77,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_74])).

tff(c_78,plain,(
    ! [A_32,B_33,C_34] :
      ( k1_relset_1(A_32,B_33,C_34) = k1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_82,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_78])).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_63,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_83,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_63])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_83])).

tff(c_87,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_94,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_87])).

tff(c_14,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_124,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k2_relat_1(A_47),k2_relat_1(B_48))
      | ~ r1_tarski(A_47,B_48)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,(
    ! [A_10,B_48] :
      ( r1_tarski(A_10,k2_relat_1(B_48))
      | ~ r1_tarski(k6_relat_1(A_10),B_48)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_124])).

tff(c_135,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,k2_relat_1(B_50))
      | ~ r1_tarski(k6_relat_1(A_49),B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_127])).

tff(c_138,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_135])).

tff(c_141,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_138])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.57  
% 2.36/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.58  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.36/1.58  
% 2.36/1.58  %Foreground sorts:
% 2.36/1.58  
% 2.36/1.58  
% 2.36/1.58  %Background operators:
% 2.36/1.58  
% 2.36/1.58  
% 2.36/1.58  %Foreground operators:
% 2.36/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.36/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.36/1.58  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.58  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.58  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.36/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.58  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.36/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.58  
% 2.36/1.60  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 2.36/1.60  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.36/1.60  tff(f_36, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.36/1.60  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.36/1.60  tff(f_34, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.36/1.60  tff(f_51, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.36/1.60  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.36/1.60  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.36/1.60  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.36/1.60  tff(c_89, plain, (![A_35, B_36, C_37]: (k2_relset_1(A_35, B_36, C_37)=k2_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.36/1.60  tff(c_93, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_89])).
% 2.36/1.60  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.60  tff(c_45, plain, (![B_22, A_23]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.60  tff(c_48, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_45])).
% 2.36/1.60  tff(c_51, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_48])).
% 2.36/1.60  tff(c_22, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.36/1.60  tff(c_4, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.36/1.60  tff(c_12, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.36/1.60  tff(c_52, plain, (![A_24, B_25]: (r1_tarski(k1_relat_1(A_24), k1_relat_1(B_25)) | ~r1_tarski(A_24, B_25) | ~v1_relat_1(B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.36/1.60  tff(c_55, plain, (![A_10, B_25]: (r1_tarski(A_10, k1_relat_1(B_25)) | ~r1_tarski(k6_relat_1(A_10), B_25) | ~v1_relat_1(B_25) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_52])).
% 2.36/1.60  tff(c_71, plain, (![A_30, B_31]: (r1_tarski(A_30, k1_relat_1(B_31)) | ~r1_tarski(k6_relat_1(A_30), B_31) | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_55])).
% 2.36/1.60  tff(c_74, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_71])).
% 2.36/1.60  tff(c_77, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_74])).
% 2.36/1.60  tff(c_78, plain, (![A_32, B_33, C_34]: (k1_relset_1(A_32, B_33, C_34)=k1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.60  tff(c_82, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_78])).
% 2.36/1.60  tff(c_20, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.36/1.60  tff(c_63, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_20])).
% 2.36/1.60  tff(c_83, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_63])).
% 2.36/1.60  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_83])).
% 2.36/1.60  tff(c_87, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_20])).
% 2.36/1.60  tff(c_94, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_87])).
% 2.36/1.60  tff(c_14, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.36/1.60  tff(c_124, plain, (![A_47, B_48]: (r1_tarski(k2_relat_1(A_47), k2_relat_1(B_48)) | ~r1_tarski(A_47, B_48) | ~v1_relat_1(B_48) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.36/1.60  tff(c_127, plain, (![A_10, B_48]: (r1_tarski(A_10, k2_relat_1(B_48)) | ~r1_tarski(k6_relat_1(A_10), B_48) | ~v1_relat_1(B_48) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_124])).
% 2.36/1.60  tff(c_135, plain, (![A_49, B_50]: (r1_tarski(A_49, k2_relat_1(B_50)) | ~r1_tarski(k6_relat_1(A_49), B_50) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_127])).
% 2.36/1.60  tff(c_138, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_135])).
% 2.36/1.60  tff(c_141, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_138])).
% 2.36/1.60  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_141])).
% 2.36/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.60  
% 2.36/1.60  Inference rules
% 2.36/1.60  ----------------------
% 2.36/1.60  #Ref     : 0
% 2.36/1.60  #Sup     : 21
% 2.36/1.60  #Fact    : 0
% 2.36/1.60  #Define  : 0
% 2.36/1.60  #Split   : 1
% 2.36/1.60  #Chain   : 0
% 2.36/1.60  #Close   : 0
% 2.36/1.60  
% 2.36/1.60  Ordering : KBO
% 2.36/1.60  
% 2.36/1.60  Simplification rules
% 2.36/1.60  ----------------------
% 2.36/1.60  #Subsume      : 0
% 2.36/1.60  #Demod        : 15
% 2.36/1.60  #Tautology    : 9
% 2.36/1.60  #SimpNegUnit  : 1
% 2.36/1.60  #BackRed      : 3
% 2.36/1.60  
% 2.36/1.60  #Partial instantiations: 0
% 2.36/1.60  #Strategies tried      : 1
% 2.36/1.60  
% 2.36/1.60  Timing (in seconds)
% 2.36/1.60  ----------------------
% 2.36/1.60  Preprocessing        : 0.45
% 2.36/1.60  Parsing              : 0.24
% 2.36/1.60  CNF conversion       : 0.03
% 2.36/1.61  Main loop            : 0.24
% 2.36/1.61  Inferencing          : 0.09
% 2.36/1.61  Reduction            : 0.08
% 2.36/1.61  Demodulation         : 0.06
% 2.36/1.61  BG Simplification    : 0.02
% 2.36/1.61  Subsumption          : 0.03
% 2.36/1.61  Abstraction          : 0.01
% 2.36/1.61  MUC search           : 0.00
% 2.36/1.61  Cooper               : 0.00
% 2.36/1.61  Total                : 0.75
% 2.36/1.61  Index Insertion      : 0.00
% 2.36/1.61  Index Deletion       : 0.00
% 2.36/1.61  Index Matching       : 0.00
% 2.36/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
