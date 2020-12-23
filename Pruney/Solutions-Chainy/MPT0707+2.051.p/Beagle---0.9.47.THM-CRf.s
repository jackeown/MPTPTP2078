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
% DateTime   : Thu Dec  3 10:05:22 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  92 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_44])).

tff(c_14,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_7] : k2_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_9] : v1_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_148,plain,(
    ! [B_29,A_30] :
      ( k9_relat_1(B_29,k10_relat_1(B_29,A_30)) = A_30
      | ~ r1_tarski(A_30,k2_relat_1(B_29))
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_150,plain,(
    ! [A_7,A_30] :
      ( k9_relat_1(k6_relat_1(A_7),k10_relat_1(k6_relat_1(A_7),A_30)) = A_30
      | ~ r1_tarski(A_30,A_7)
      | ~ v1_funct_1(k6_relat_1(A_7))
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_148])).

tff(c_153,plain,(
    ! [A_31,A_32] :
      ( k9_relat_1(k6_relat_1(A_31),k10_relat_1(k6_relat_1(A_31),A_32)) = A_32
      | ~ r1_tarski(A_32,A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_150])).

tff(c_12,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k6_relat_1(k2_relat_1(A_8))) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_76,plain,(
    ! [B_22,C_23,A_24] :
      ( k9_relat_1(k5_relat_1(B_22,C_23),A_24) = k9_relat_1(C_23,k9_relat_1(B_22,A_24))
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_88,plain,(
    ! [A_8,A_24] :
      ( k9_relat_1(k6_relat_1(k2_relat_1(A_8)),k9_relat_1(A_8,A_24)) = k9_relat_1(A_8,A_24)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_8)))
      | ~ v1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_76])).

tff(c_94,plain,(
    ! [A_8,A_24] :
      ( k9_relat_1(k6_relat_1(k2_relat_1(A_8)),k9_relat_1(A_8,A_24)) = k9_relat_1(A_8,A_24)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_88])).

tff(c_159,plain,(
    ! [A_31,A_32] :
      ( k9_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_31))),A_32) = k9_relat_1(k6_relat_1(A_31),k10_relat_1(k6_relat_1(A_31),A_32))
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ r1_tarski(A_32,A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_94])).

tff(c_170,plain,(
    ! [A_33,A_34] :
      ( k9_relat_1(k6_relat_1(A_33),k10_relat_1(k6_relat_1(A_33),A_34)) = k9_relat_1(k6_relat_1(A_33),A_34)
      | ~ r1_tarski(A_34,A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10,c_159])).

tff(c_152,plain,(
    ! [A_7,A_30] :
      ( k9_relat_1(k6_relat_1(A_7),k10_relat_1(k6_relat_1(A_7),A_30)) = A_30
      | ~ r1_tarski(A_30,A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_150])).

tff(c_194,plain,(
    ! [A_35,A_36] :
      ( k9_relat_1(k6_relat_1(A_35),A_36) = A_36
      | ~ r1_tarski(A_36,A_35)
      | ~ r1_tarski(A_36,A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_152])).

tff(c_20,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_221,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_20])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.53  
% 2.38/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.53  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.38/1.53  
% 2.38/1.53  %Foreground sorts:
% 2.38/1.53  
% 2.38/1.53  
% 2.38/1.53  %Background operators:
% 2.38/1.53  
% 2.38/1.53  
% 2.38/1.53  %Foreground operators:
% 2.38/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.38/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.38/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.38/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.38/1.53  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.38/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.38/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.53  
% 2.40/1.55  tff(f_61, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.40/1.55  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.40/1.55  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.40/1.55  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.40/1.55  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.40/1.55  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 2.40/1.55  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 2.40/1.55  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.40/1.55  tff(c_44, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.55  tff(c_52, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_44])).
% 2.40/1.55  tff(c_14, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.40/1.55  tff(c_10, plain, (![A_7]: (k2_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.40/1.55  tff(c_16, plain, (![A_9]: (v1_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.40/1.55  tff(c_148, plain, (![B_29, A_30]: (k9_relat_1(B_29, k10_relat_1(B_29, A_30))=A_30 | ~r1_tarski(A_30, k2_relat_1(B_29)) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.40/1.55  tff(c_150, plain, (![A_7, A_30]: (k9_relat_1(k6_relat_1(A_7), k10_relat_1(k6_relat_1(A_7), A_30))=A_30 | ~r1_tarski(A_30, A_7) | ~v1_funct_1(k6_relat_1(A_7)) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_148])).
% 2.40/1.55  tff(c_153, plain, (![A_31, A_32]: (k9_relat_1(k6_relat_1(A_31), k10_relat_1(k6_relat_1(A_31), A_32))=A_32 | ~r1_tarski(A_32, A_31))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_150])).
% 2.40/1.55  tff(c_12, plain, (![A_8]: (k5_relat_1(A_8, k6_relat_1(k2_relat_1(A_8)))=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.40/1.55  tff(c_76, plain, (![B_22, C_23, A_24]: (k9_relat_1(k5_relat_1(B_22, C_23), A_24)=k9_relat_1(C_23, k9_relat_1(B_22, A_24)) | ~v1_relat_1(C_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.40/1.55  tff(c_88, plain, (![A_8, A_24]: (k9_relat_1(k6_relat_1(k2_relat_1(A_8)), k9_relat_1(A_8, A_24))=k9_relat_1(A_8, A_24) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_8))) | ~v1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_76])).
% 2.40/1.55  tff(c_94, plain, (![A_8, A_24]: (k9_relat_1(k6_relat_1(k2_relat_1(A_8)), k9_relat_1(A_8, A_24))=k9_relat_1(A_8, A_24) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_88])).
% 2.40/1.55  tff(c_159, plain, (![A_31, A_32]: (k9_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_31))), A_32)=k9_relat_1(k6_relat_1(A_31), k10_relat_1(k6_relat_1(A_31), A_32)) | ~v1_relat_1(k6_relat_1(A_31)) | ~r1_tarski(A_32, A_31))), inference(superposition, [status(thm), theory('equality')], [c_153, c_94])).
% 2.40/1.55  tff(c_170, plain, (![A_33, A_34]: (k9_relat_1(k6_relat_1(A_33), k10_relat_1(k6_relat_1(A_33), A_34))=k9_relat_1(k6_relat_1(A_33), A_34) | ~r1_tarski(A_34, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_10, c_159])).
% 2.40/1.55  tff(c_152, plain, (![A_7, A_30]: (k9_relat_1(k6_relat_1(A_7), k10_relat_1(k6_relat_1(A_7), A_30))=A_30 | ~r1_tarski(A_30, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_150])).
% 2.40/1.55  tff(c_194, plain, (![A_35, A_36]: (k9_relat_1(k6_relat_1(A_35), A_36)=A_36 | ~r1_tarski(A_36, A_35) | ~r1_tarski(A_36, A_35))), inference(superposition, [status(thm), theory('equality')], [c_170, c_152])).
% 2.40/1.55  tff(c_20, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.40/1.55  tff(c_221, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_194, c_20])).
% 2.40/1.55  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_221])).
% 2.40/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.55  
% 2.40/1.55  Inference rules
% 2.40/1.55  ----------------------
% 2.40/1.55  #Ref     : 0
% 2.40/1.55  #Sup     : 51
% 2.40/1.55  #Fact    : 0
% 2.40/1.55  #Define  : 0
% 2.40/1.55  #Split   : 0
% 2.40/1.55  #Chain   : 0
% 2.40/1.55  #Close   : 0
% 2.40/1.55  
% 2.40/1.55  Ordering : KBO
% 2.40/1.55  
% 2.40/1.55  Simplification rules
% 2.40/1.55  ----------------------
% 2.40/1.55  #Subsume      : 2
% 2.40/1.55  #Demod        : 27
% 2.40/1.55  #Tautology    : 31
% 2.40/1.55  #SimpNegUnit  : 0
% 2.40/1.55  #BackRed      : 0
% 2.40/1.55  
% 2.40/1.55  #Partial instantiations: 0
% 2.40/1.55  #Strategies tried      : 1
% 2.40/1.55  
% 2.40/1.55  Timing (in seconds)
% 2.40/1.55  ----------------------
% 2.40/1.56  Preprocessing        : 0.45
% 2.40/1.56  Parsing              : 0.25
% 2.40/1.56  CNF conversion       : 0.03
% 2.40/1.56  Main loop            : 0.28
% 2.40/1.56  Inferencing          : 0.13
% 2.40/1.56  Reduction            : 0.08
% 2.40/1.56  Demodulation         : 0.06
% 2.40/1.56  BG Simplification    : 0.02
% 2.40/1.56  Subsumption          : 0.04
% 2.40/1.56  Abstraction          : 0.02
% 2.40/1.56  MUC search           : 0.00
% 2.40/1.56  Cooper               : 0.00
% 2.40/1.56  Total                : 0.78
% 2.40/1.56  Index Insertion      : 0.00
% 2.40/1.56  Index Deletion       : 0.00
% 2.40/1.56  Index Matching       : 0.00
% 2.40/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
