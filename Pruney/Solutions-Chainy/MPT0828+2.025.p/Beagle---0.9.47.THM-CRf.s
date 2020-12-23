%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:20 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   55 (  83 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 139 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_relset_1(A_34,B_35,C_36) = k1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_56])).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_43,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_65,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_43])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_29,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_26])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_29])).

tff(c_38,plain,(
    ! [C_27,A_28,B_29] :
      ( v4_relat_1(C_27,A_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_38])).

tff(c_44,plain,(
    ! [B_30,A_31] :
      ( k7_relat_1(B_30,A_31) = B_30
      | ~ v4_relat_1(B_30,A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_47,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_44])).

tff(c_50,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_47])).

tff(c_22,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_75,plain,(
    ! [C_43,A_44,B_45,D_46] :
      ( r1_tarski(C_43,k1_relset_1(A_44,B_45,D_46))
      | ~ r1_tarski(k6_relat_1(C_43),D_46)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_79,plain,(
    ! [A_47,B_48] :
      ( r1_tarski('#skF_2',k1_relset_1(A_47,B_48,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(resolution,[status(thm)],[c_22,c_75])).

tff(c_82,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_79])).

tff(c_84,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_82])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k1_relat_1(k7_relat_1(B_9,A_8)) = A_8
      | ~ r1_tarski(A_8,k1_relat_1(B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_8])).

tff(c_90,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50,c_87])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_90])).

tff(c_93,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_142,plain,(
    ! [C_57,A_58,B_59,D_60] :
      ( r1_tarski(C_57,k2_relset_1(A_58,B_59,D_60))
      | ~ r1_tarski(k6_relat_1(C_57),D_60)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_146,plain,(
    ! [A_61,B_62] :
      ( r1_tarski('#skF_2',k2_relset_1(A_61,B_62,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(resolution,[status(thm)],[c_22,c_142])).

tff(c_149,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_146])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.27  
% 1.93/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.27  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.27  
% 1.93/1.27  %Foreground sorts:
% 1.93/1.27  
% 1.93/1.27  
% 1.93/1.27  %Background operators:
% 1.93/1.27  
% 1.93/1.27  
% 1.93/1.27  %Foreground operators:
% 1.93/1.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.93/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.93/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.93/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.93/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.27  
% 1.93/1.28  tff(f_73, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relset_1)).
% 1.93/1.28  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.93/1.28  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.93/1.28  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.93/1.28  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.93/1.28  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.93/1.28  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 1.93/1.28  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 1.93/1.28  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.93/1.28  tff(c_56, plain, (![A_34, B_35, C_36]: (k1_relset_1(A_34, B_35, C_36)=k1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.28  tff(c_60, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_56])).
% 1.93/1.28  tff(c_20, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.93/1.28  tff(c_43, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_20])).
% 1.93/1.28  tff(c_65, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_43])).
% 1.93/1.28  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.28  tff(c_26, plain, (![B_22, A_23]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.28  tff(c_29, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_26])).
% 1.93/1.28  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_29])).
% 1.93/1.28  tff(c_38, plain, (![C_27, A_28, B_29]: (v4_relat_1(C_27, A_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.28  tff(c_42, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_38])).
% 1.93/1.28  tff(c_44, plain, (![B_30, A_31]: (k7_relat_1(B_30, A_31)=B_30 | ~v4_relat_1(B_30, A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.93/1.28  tff(c_47, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_44])).
% 1.93/1.28  tff(c_50, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_47])).
% 1.93/1.28  tff(c_22, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.93/1.28  tff(c_75, plain, (![C_43, A_44, B_45, D_46]: (r1_tarski(C_43, k1_relset_1(A_44, B_45, D_46)) | ~r1_tarski(k6_relat_1(C_43), D_46) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.93/1.28  tff(c_79, plain, (![A_47, B_48]: (r1_tarski('#skF_2', k1_relset_1(A_47, B_48, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(resolution, [status(thm)], [c_22, c_75])).
% 1.93/1.28  tff(c_82, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_79])).
% 1.93/1.28  tff(c_84, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_82])).
% 1.93/1.28  tff(c_8, plain, (![B_9, A_8]: (k1_relat_1(k7_relat_1(B_9, A_8))=A_8 | ~r1_tarski(A_8, k1_relat_1(B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.93/1.28  tff(c_87, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_8])).
% 1.93/1.28  tff(c_90, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50, c_87])).
% 1.93/1.28  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_90])).
% 1.93/1.28  tff(c_93, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_20])).
% 1.93/1.28  tff(c_142, plain, (![C_57, A_58, B_59, D_60]: (r1_tarski(C_57, k2_relset_1(A_58, B_59, D_60)) | ~r1_tarski(k6_relat_1(C_57), D_60) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.93/1.28  tff(c_146, plain, (![A_61, B_62]: (r1_tarski('#skF_2', k2_relset_1(A_61, B_62, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(resolution, [status(thm)], [c_22, c_142])).
% 1.93/1.28  tff(c_149, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_146])).
% 1.93/1.28  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_149])).
% 1.93/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.28  
% 1.93/1.28  Inference rules
% 1.93/1.28  ----------------------
% 1.93/1.28  #Ref     : 0
% 1.93/1.28  #Sup     : 29
% 1.93/1.28  #Fact    : 0
% 1.93/1.28  #Define  : 0
% 1.93/1.28  #Split   : 1
% 1.93/1.28  #Chain   : 0
% 1.93/1.28  #Close   : 0
% 1.93/1.28  
% 1.93/1.28  Ordering : KBO
% 1.93/1.28  
% 1.93/1.28  Simplification rules
% 1.93/1.28  ----------------------
% 1.93/1.28  #Subsume      : 0
% 1.93/1.28  #Demod        : 10
% 1.93/1.28  #Tautology    : 13
% 1.93/1.28  #SimpNegUnit  : 2
% 1.93/1.28  #BackRed      : 1
% 1.93/1.28  
% 1.93/1.28  #Partial instantiations: 0
% 1.93/1.28  #Strategies tried      : 1
% 1.93/1.28  
% 1.93/1.28  Timing (in seconds)
% 1.93/1.28  ----------------------
% 1.93/1.29  Preprocessing        : 0.32
% 1.93/1.29  Parsing              : 0.17
% 1.93/1.29  CNF conversion       : 0.02
% 1.93/1.29  Main loop            : 0.15
% 1.93/1.29  Inferencing          : 0.06
% 1.93/1.29  Reduction            : 0.05
% 1.93/1.29  Demodulation         : 0.03
% 1.93/1.29  BG Simplification    : 0.01
% 1.93/1.29  Subsumption          : 0.02
% 1.93/1.29  Abstraction          : 0.01
% 1.93/1.29  MUC search           : 0.00
% 1.93/1.29  Cooper               : 0.00
% 1.93/1.29  Total                : 0.49
% 1.93/1.29  Index Insertion      : 0.00
% 1.93/1.29  Index Deletion       : 0.00
% 1.93/1.29  Index Matching       : 0.00
% 1.93/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
