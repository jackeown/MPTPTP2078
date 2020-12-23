%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:22 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   50 (  70 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 119 expanded)
%              Number of equality atoms :   12 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_210,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_214,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_210])).

tff(c_24,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_52,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_148,plain,(
    ! [C_46,A_47,B_48,D_49] :
      ( r1_tarski(C_46,k1_relset_1(A_47,B_48,D_49))
      | ~ r1_tarski(k6_relat_1(C_46),D_49)
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_176,plain,(
    ! [A_52,B_53] :
      ( r1_tarski('#skF_2',k1_relset_1(A_52,B_53,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(resolution,[status(thm)],[c_26,c_148])).

tff(c_179,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_176])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_179])).

tff(c_184,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_215,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_184])).

tff(c_31,plain,(
    ! [C_19,A_20,B_21] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_35,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_31])).

tff(c_203,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_207,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_203])).

tff(c_240,plain,(
    ! [C_71,A_72,B_73,D_74] :
      ( r1_tarski(C_71,k2_relset_1(A_72,B_73,D_74))
      | ~ r1_tarski(k6_relat_1(C_71),D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_254,plain,(
    ! [A_77,B_78] :
      ( r1_tarski('#skF_2',k2_relset_1(A_77,B_78,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(resolution,[status(thm)],[c_26,c_240])).

tff(c_257,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_254])).

tff(c_259,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_257])).

tff(c_189,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(k2_relat_1(B_54),A_55)
      | ~ v5_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_192,plain,(
    ! [B_54,A_55] :
      ( k2_relat_1(B_54) = A_55
      | ~ r1_tarski(A_55,k2_relat_1(B_54))
      | ~ v5_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_189,c_2])).

tff(c_262,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_259,c_192])).

tff(c_267,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_207,c_262])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.04/1.30  
% 2.04/1.30  %Foreground sorts:
% 2.04/1.30  
% 2.04/1.30  
% 2.04/1.30  %Background operators:
% 2.04/1.30  
% 2.04/1.30  
% 2.04/1.30  %Foreground operators:
% 2.04/1.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.04/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.04/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.04/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.30  
% 2.04/1.31  tff(f_68, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relset_1)).
% 2.04/1.31  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.04/1.31  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 2.04/1.31  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.04/1.31  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.04/1.31  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.04/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.04/1.31  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.04/1.31  tff(c_210, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.31  tff(c_214, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_210])).
% 2.04/1.31  tff(c_24, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.04/1.31  tff(c_52, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_24])).
% 2.04/1.31  tff(c_26, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.04/1.31  tff(c_148, plain, (![C_46, A_47, B_48, D_49]: (r1_tarski(C_46, k1_relset_1(A_47, B_48, D_49)) | ~r1_tarski(k6_relat_1(C_46), D_49) | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.31  tff(c_176, plain, (![A_52, B_53]: (r1_tarski('#skF_2', k1_relset_1(A_52, B_53, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(resolution, [status(thm)], [c_26, c_148])).
% 2.04/1.31  tff(c_179, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_176])).
% 2.04/1.31  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_179])).
% 2.04/1.31  tff(c_184, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.04/1.31  tff(c_215, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_214, c_184])).
% 2.04/1.31  tff(c_31, plain, (![C_19, A_20, B_21]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.31  tff(c_35, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_31])).
% 2.04/1.31  tff(c_203, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.04/1.31  tff(c_207, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_203])).
% 2.04/1.31  tff(c_240, plain, (![C_71, A_72, B_73, D_74]: (r1_tarski(C_71, k2_relset_1(A_72, B_73, D_74)) | ~r1_tarski(k6_relat_1(C_71), D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.31  tff(c_254, plain, (![A_77, B_78]: (r1_tarski('#skF_2', k2_relset_1(A_77, B_78, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(resolution, [status(thm)], [c_26, c_240])).
% 2.04/1.31  tff(c_257, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_254])).
% 2.04/1.31  tff(c_259, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_257])).
% 2.04/1.31  tff(c_189, plain, (![B_54, A_55]: (r1_tarski(k2_relat_1(B_54), A_55) | ~v5_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.31  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.31  tff(c_192, plain, (![B_54, A_55]: (k2_relat_1(B_54)=A_55 | ~r1_tarski(A_55, k2_relat_1(B_54)) | ~v5_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_189, c_2])).
% 2.04/1.31  tff(c_262, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_259, c_192])).
% 2.04/1.31  tff(c_267, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_207, c_262])).
% 2.04/1.31  tff(c_269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_267])).
% 2.04/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.31  
% 2.04/1.31  Inference rules
% 2.04/1.31  ----------------------
% 2.04/1.31  #Ref     : 0
% 2.04/1.31  #Sup     : 50
% 2.04/1.31  #Fact    : 0
% 2.04/1.31  #Define  : 0
% 2.04/1.31  #Split   : 3
% 2.04/1.31  #Chain   : 0
% 2.04/1.31  #Close   : 0
% 2.04/1.31  
% 2.04/1.31  Ordering : KBO
% 2.04/1.31  
% 2.04/1.31  Simplification rules
% 2.04/1.31  ----------------------
% 2.04/1.31  #Subsume      : 0
% 2.04/1.31  #Demod        : 26
% 2.04/1.31  #Tautology    : 21
% 2.04/1.31  #SimpNegUnit  : 2
% 2.04/1.31  #BackRed      : 3
% 2.04/1.31  
% 2.04/1.31  #Partial instantiations: 0
% 2.04/1.31  #Strategies tried      : 1
% 2.04/1.31  
% 2.04/1.31  Timing (in seconds)
% 2.04/1.31  ----------------------
% 2.04/1.32  Preprocessing        : 0.30
% 2.04/1.32  Parsing              : 0.17
% 2.04/1.32  CNF conversion       : 0.02
% 2.04/1.32  Main loop            : 0.19
% 2.04/1.32  Inferencing          : 0.07
% 2.04/1.32  Reduction            : 0.06
% 2.04/1.32  Demodulation         : 0.04
% 2.04/1.32  BG Simplification    : 0.01
% 2.04/1.32  Subsumption          : 0.04
% 2.04/1.32  Abstraction          : 0.01
% 2.04/1.32  MUC search           : 0.00
% 2.04/1.32  Cooper               : 0.00
% 2.04/1.32  Total                : 0.53
% 2.04/1.32  Index Insertion      : 0.00
% 2.04/1.32  Index Deletion       : 0.00
% 2.04/1.32  Index Matching       : 0.00
% 2.04/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
