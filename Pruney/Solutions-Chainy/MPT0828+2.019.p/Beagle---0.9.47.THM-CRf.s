%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:19 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   53 (  73 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 ( 125 expanded)
%              Number of equality atoms :   12 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
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

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_78,plain,(
    ! [A_38,B_39,C_40] :
      ( k1_relset_1(A_38,B_39,C_40) = k1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_78])).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_52,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_83,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_52])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [B_23,A_24] :
      ( v1_relat_1(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_24))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_37,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_34])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_37])).

tff(c_57,plain,(
    ! [C_29,A_30,B_31] :
      ( v4_relat_1(C_29,A_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_61,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_28,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_116,plain,(
    ! [C_49,A_50,B_51,D_52] :
      ( r1_tarski(C_49,k1_relset_1(A_50,B_51,D_52))
      | ~ r1_tarski(k6_relat_1(C_49),D_52)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_125,plain,(
    ! [A_53,B_54] :
      ( r1_tarski('#skF_2',k1_relset_1(A_53,B_54,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(resolution,[status(thm)],[c_28,c_116])).

tff(c_128,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_125])).

tff(c_130,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_128])).

tff(c_53,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(k1_relat_1(B_27),A_28)
      | ~ v4_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [B_27,A_28] :
      ( k1_relat_1(B_27) = A_28
      | ~ r1_tarski(A_28,k1_relat_1(B_27))
      | ~ v4_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_133,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v4_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_56])).

tff(c_138,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_61,c_133])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_138])).

tff(c_141,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_266,plain,(
    ! [C_83,A_84,B_85,D_86] :
      ( r1_tarski(C_83,k2_relset_1(A_84,B_85,D_86))
      | ~ r1_tarski(k6_relat_1(C_83),D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_274,plain,(
    ! [A_87,B_88] :
      ( r1_tarski('#skF_2',k2_relset_1(A_87,B_88,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(resolution,[status(thm)],[c_28,c_266])).

tff(c_277,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_274])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.30  
% 2.10/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.30  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.10/1.30  
% 2.10/1.30  %Foreground sorts:
% 2.10/1.30  
% 2.10/1.30  
% 2.10/1.30  %Background operators:
% 2.10/1.30  
% 2.10/1.30  
% 2.10/1.30  %Foreground operators:
% 2.10/1.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.10/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.10/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.10/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.30  
% 2.29/1.31  tff(f_73, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relset_1)).
% 2.29/1.31  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.29/1.31  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.29/1.31  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.29/1.31  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.29/1.31  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 2.29/1.31  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.29/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.29/1.31  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.29/1.31  tff(c_78, plain, (![A_38, B_39, C_40]: (k1_relset_1(A_38, B_39, C_40)=k1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.29/1.31  tff(c_82, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_78])).
% 2.29/1.31  tff(c_26, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.29/1.31  tff(c_52, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 2.29/1.31  tff(c_83, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_52])).
% 2.29/1.31  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.29/1.31  tff(c_34, plain, (![B_23, A_24]: (v1_relat_1(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_24)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.29/1.31  tff(c_37, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_34])).
% 2.29/1.31  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_37])).
% 2.29/1.31  tff(c_57, plain, (![C_29, A_30, B_31]: (v4_relat_1(C_29, A_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.31  tff(c_61, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_57])).
% 2.29/1.31  tff(c_28, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.29/1.31  tff(c_116, plain, (![C_49, A_50, B_51, D_52]: (r1_tarski(C_49, k1_relset_1(A_50, B_51, D_52)) | ~r1_tarski(k6_relat_1(C_49), D_52) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.31  tff(c_125, plain, (![A_53, B_54]: (r1_tarski('#skF_2', k1_relset_1(A_53, B_54, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(resolution, [status(thm)], [c_28, c_116])).
% 2.29/1.31  tff(c_128, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_125])).
% 2.29/1.31  tff(c_130, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_128])).
% 2.29/1.31  tff(c_53, plain, (![B_27, A_28]: (r1_tarski(k1_relat_1(B_27), A_28) | ~v4_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.31  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.31  tff(c_56, plain, (![B_27, A_28]: (k1_relat_1(B_27)=A_28 | ~r1_tarski(A_28, k1_relat_1(B_27)) | ~v4_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_53, c_2])).
% 2.29/1.31  tff(c_133, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v4_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_56])).
% 2.29/1.31  tff(c_138, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_61, c_133])).
% 2.29/1.31  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_138])).
% 2.29/1.31  tff(c_141, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_26])).
% 2.29/1.31  tff(c_266, plain, (![C_83, A_84, B_85, D_86]: (r1_tarski(C_83, k2_relset_1(A_84, B_85, D_86)) | ~r1_tarski(k6_relat_1(C_83), D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.31  tff(c_274, plain, (![A_87, B_88]: (r1_tarski('#skF_2', k2_relset_1(A_87, B_88, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(resolution, [status(thm)], [c_28, c_266])).
% 2.29/1.31  tff(c_277, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_274])).
% 2.29/1.31  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_277])).
% 2.29/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  Inference rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Ref     : 0
% 2.29/1.31  #Sup     : 50
% 2.29/1.31  #Fact    : 0
% 2.29/1.31  #Define  : 0
% 2.29/1.31  #Split   : 3
% 2.29/1.31  #Chain   : 0
% 2.29/1.31  #Close   : 0
% 2.29/1.31  
% 2.29/1.31  Ordering : KBO
% 2.29/1.31  
% 2.29/1.31  Simplification rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Subsume      : 1
% 2.29/1.31  #Demod        : 25
% 2.29/1.31  #Tautology    : 19
% 2.29/1.31  #SimpNegUnit  : 2
% 2.29/1.31  #BackRed      : 1
% 2.29/1.31  
% 2.29/1.31  #Partial instantiations: 0
% 2.29/1.31  #Strategies tried      : 1
% 2.29/1.31  
% 2.29/1.31  Timing (in seconds)
% 2.29/1.31  ----------------------
% 2.29/1.31  Preprocessing        : 0.31
% 2.29/1.31  Parsing              : 0.16
% 2.29/1.32  CNF conversion       : 0.02
% 2.29/1.32  Main loop            : 0.22
% 2.29/1.32  Inferencing          : 0.08
% 2.29/1.32  Reduction            : 0.07
% 2.29/1.32  Demodulation         : 0.05
% 2.29/1.32  BG Simplification    : 0.01
% 2.29/1.32  Subsumption          : 0.04
% 2.29/1.32  Abstraction          : 0.01
% 2.29/1.32  MUC search           : 0.00
% 2.29/1.32  Cooper               : 0.00
% 2.29/1.32  Total                : 0.57
% 2.29/1.32  Index Insertion      : 0.00
% 2.29/1.32  Index Deletion       : 0.00
% 2.29/1.32  Index Matching       : 0.00
% 2.29/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
