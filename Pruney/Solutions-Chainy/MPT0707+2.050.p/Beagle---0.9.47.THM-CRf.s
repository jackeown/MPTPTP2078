%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:22 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   42 (  62 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  84 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_44])).

tff(c_16,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_53,plain,(
    ! [A_20] :
      ( k9_relat_1(A_20,k1_relat_1(A_20)) = k2_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    ! [A_8] :
      ( k9_relat_1(k6_relat_1(A_8),A_8) = k2_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_66,plain,(
    ! [A_8] : k9_relat_1(k6_relat_1(A_8),A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12,c_62])).

tff(c_76,plain,(
    ! [B_22,A_23] :
      ( k5_relat_1(B_22,k6_relat_1(A_23)) = B_22
      | ~ r1_tarski(k2_relat_1(B_22),A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    ! [A_8,A_23] :
      ( k5_relat_1(k6_relat_1(A_8),k6_relat_1(A_23)) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_23)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_76])).

tff(c_81,plain,(
    ! [A_8,A_23] :
      ( k5_relat_1(k6_relat_1(A_8),k6_relat_1(A_23)) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_91,plain,(
    ! [B_26,C_27,A_28] :
      ( k9_relat_1(k5_relat_1(B_26,C_27),A_28) = k9_relat_1(C_27,k9_relat_1(B_26,A_28))
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_104,plain,(
    ! [A_23,A_8,A_28] :
      ( k9_relat_1(k6_relat_1(A_23),k9_relat_1(k6_relat_1(A_8),A_28)) = k9_relat_1(k6_relat_1(A_8),A_28)
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ r1_tarski(A_8,A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_91])).

tff(c_113,plain,(
    ! [A_29,A_30,A_31] :
      ( k9_relat_1(k6_relat_1(A_29),k9_relat_1(k6_relat_1(A_30),A_31)) = k9_relat_1(k6_relat_1(A_30),A_31)
      | ~ r1_tarski(A_30,A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_104])).

tff(c_132,plain,(
    ! [A_8,A_29] :
      ( k9_relat_1(k6_relat_1(A_8),A_8) = k9_relat_1(k6_relat_1(A_29),A_8)
      | ~ r1_tarski(A_8,A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_113])).

tff(c_192,plain,(
    ! [A_34,A_35] :
      ( k9_relat_1(k6_relat_1(A_34),A_35) = A_35
      | ~ r1_tarski(A_35,A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_132])).

tff(c_20,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_221,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_20])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.22  
% 1.74/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.22  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.74/1.22  
% 1.74/1.22  %Foreground sorts:
% 1.74/1.22  
% 1.74/1.22  
% 1.74/1.22  %Background operators:
% 1.74/1.22  
% 1.74/1.22  
% 1.74/1.22  %Foreground operators:
% 1.74/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.74/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.74/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.74/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.74/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.74/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.74/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.74/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.74/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.74/1.22  
% 1.74/1.23  tff(f_59, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 1.74/1.23  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.74/1.23  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.74/1.23  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.74/1.23  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 1.74/1.23  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 1.74/1.23  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 1.74/1.23  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.74/1.23  tff(c_44, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.74/1.23  tff(c_52, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_44])).
% 1.74/1.23  tff(c_16, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.74/1.23  tff(c_12, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.74/1.23  tff(c_10, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.74/1.23  tff(c_53, plain, (![A_20]: (k9_relat_1(A_20, k1_relat_1(A_20))=k2_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.74/1.23  tff(c_62, plain, (![A_8]: (k9_relat_1(k6_relat_1(A_8), A_8)=k2_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_53])).
% 1.74/1.23  tff(c_66, plain, (![A_8]: (k9_relat_1(k6_relat_1(A_8), A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12, c_62])).
% 1.74/1.23  tff(c_76, plain, (![B_22, A_23]: (k5_relat_1(B_22, k6_relat_1(A_23))=B_22 | ~r1_tarski(k2_relat_1(B_22), A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.74/1.23  tff(c_79, plain, (![A_8, A_23]: (k5_relat_1(k6_relat_1(A_8), k6_relat_1(A_23))=k6_relat_1(A_8) | ~r1_tarski(A_8, A_23) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_76])).
% 1.74/1.23  tff(c_81, plain, (![A_8, A_23]: (k5_relat_1(k6_relat_1(A_8), k6_relat_1(A_23))=k6_relat_1(A_8) | ~r1_tarski(A_8, A_23))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_79])).
% 1.74/1.23  tff(c_91, plain, (![B_26, C_27, A_28]: (k9_relat_1(k5_relat_1(B_26, C_27), A_28)=k9_relat_1(C_27, k9_relat_1(B_26, A_28)) | ~v1_relat_1(C_27) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.74/1.23  tff(c_104, plain, (![A_23, A_8, A_28]: (k9_relat_1(k6_relat_1(A_23), k9_relat_1(k6_relat_1(A_8), A_28))=k9_relat_1(k6_relat_1(A_8), A_28) | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_8)) | ~r1_tarski(A_8, A_23))), inference(superposition, [status(thm), theory('equality')], [c_81, c_91])).
% 1.74/1.23  tff(c_113, plain, (![A_29, A_30, A_31]: (k9_relat_1(k6_relat_1(A_29), k9_relat_1(k6_relat_1(A_30), A_31))=k9_relat_1(k6_relat_1(A_30), A_31) | ~r1_tarski(A_30, A_29))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_104])).
% 1.74/1.23  tff(c_132, plain, (![A_8, A_29]: (k9_relat_1(k6_relat_1(A_8), A_8)=k9_relat_1(k6_relat_1(A_29), A_8) | ~r1_tarski(A_8, A_29))), inference(superposition, [status(thm), theory('equality')], [c_66, c_113])).
% 1.74/1.23  tff(c_192, plain, (![A_34, A_35]: (k9_relat_1(k6_relat_1(A_34), A_35)=A_35 | ~r1_tarski(A_35, A_34))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_132])).
% 1.74/1.23  tff(c_20, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.74/1.23  tff(c_221, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_192, c_20])).
% 1.74/1.23  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_221])).
% 1.74/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.23  
% 1.74/1.23  Inference rules
% 1.74/1.23  ----------------------
% 1.74/1.23  #Ref     : 0
% 1.74/1.23  #Sup     : 49
% 1.74/1.23  #Fact    : 0
% 1.74/1.23  #Define  : 0
% 1.74/1.23  #Split   : 0
% 1.74/1.23  #Chain   : 0
% 1.74/1.23  #Close   : 0
% 1.74/1.23  
% 1.74/1.23  Ordering : KBO
% 1.74/1.23  
% 1.74/1.23  Simplification rules
% 1.74/1.23  ----------------------
% 1.74/1.23  #Subsume      : 0
% 1.74/1.23  #Demod        : 26
% 1.74/1.23  #Tautology    : 23
% 1.74/1.23  #SimpNegUnit  : 0
% 1.74/1.23  #BackRed      : 0
% 1.74/1.23  
% 1.74/1.23  #Partial instantiations: 0
% 1.74/1.23  #Strategies tried      : 1
% 1.74/1.23  
% 1.74/1.23  Timing (in seconds)
% 1.74/1.23  ----------------------
% 1.94/1.23  Preprocessing        : 0.25
% 1.94/1.23  Parsing              : 0.14
% 1.94/1.23  CNF conversion       : 0.02
% 1.94/1.23  Main loop            : 0.18
% 1.94/1.23  Inferencing          : 0.08
% 1.94/1.23  Reduction            : 0.05
% 1.94/1.23  Demodulation         : 0.04
% 1.94/1.23  BG Simplification    : 0.01
% 1.94/1.23  Subsumption          : 0.02
% 1.94/1.23  Abstraction          : 0.01
% 1.94/1.23  MUC search           : 0.00
% 1.94/1.23  Cooper               : 0.00
% 1.94/1.23  Total                : 0.46
% 1.94/1.23  Index Insertion      : 0.00
% 1.94/1.23  Index Deletion       : 0.00
% 1.94/1.23  Index Matching       : 0.00
% 1.94/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
