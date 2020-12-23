%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:06 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 104 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 262 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k7_relat_1(B_17,A_16),B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [B_25,A_26] :
      ( v1_relat_1(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26))
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    ! [A_29,B_30] :
      ( v1_relat_1(A_29)
      | ~ v1_relat_1(B_30)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_4,c_34])).

tff(c_58,plain,(
    ! [B_17,A_16] :
      ( v1_relat_1(k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(resolution,[status(thm)],[c_16,c_48])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [C_8,A_6,D_10,B_7] :
      ( r1_tarski(k7_relat_1(C_8,A_6),k7_relat_1(D_10,B_7))
      | ~ r1_tarski(A_6,B_7)
      | ~ r1_tarski(C_8,D_10)
      | ~ v1_relat_1(D_10)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_65,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k2_relat_1(A_33),k2_relat_1(B_34))
      | ~ r1_tarski(A_33,B_34)
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_90,plain,(
    ! [A_45,B_46,A_47] :
      ( r1_tarski(k2_relat_1(A_45),k9_relat_1(B_46,A_47))
      | ~ r1_tarski(A_45,k7_relat_1(B_46,A_47))
      | ~ v1_relat_1(k7_relat_1(B_46,A_47))
      | ~ v1_relat_1(A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_65])).

tff(c_126,plain,(
    ! [B_59,A_60,B_61,A_62] :
      ( r1_tarski(k9_relat_1(B_59,A_60),k9_relat_1(B_61,A_62))
      | ~ r1_tarski(k7_relat_1(B_59,A_60),k7_relat_1(B_61,A_62))
      | ~ v1_relat_1(k7_relat_1(B_61,A_62))
      | ~ v1_relat_1(k7_relat_1(B_59,A_60))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_18,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_132,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_18])).

tff(c_136,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_132])).

tff(c_137,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_140,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_137])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_140])).

tff(c_145,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_147,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_150,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_147])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_20,c_150])).

tff(c_155,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_159,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_155])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:39:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.18  
% 1.69/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.19  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.03/1.19  
% 2.03/1.19  %Foreground sorts:
% 2.03/1.19  
% 2.03/1.19  
% 2.03/1.19  %Background operators:
% 2.03/1.19  
% 2.03/1.19  
% 2.03/1.19  %Foreground operators:
% 2.03/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.03/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.03/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.03/1.19  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.19  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.19  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.19  
% 2.03/1.20  tff(f_78, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_relat_1)).
% 2.03/1.20  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.03/1.20  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.03/1.20  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.03/1.20  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 2.03/1.20  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.03/1.20  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.03/1.20  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.03/1.20  tff(c_16, plain, (![B_17, A_16]: (r1_tarski(k7_relat_1(B_17, A_16), B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.03/1.20  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.20  tff(c_34, plain, (![B_25, A_26]: (v1_relat_1(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.03/1.20  tff(c_48, plain, (![A_29, B_30]: (v1_relat_1(A_29) | ~v1_relat_1(B_30) | ~r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_4, c_34])).
% 2.03/1.20  tff(c_58, plain, (![B_17, A_16]: (v1_relat_1(k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17))), inference(resolution, [status(thm)], [c_16, c_48])).
% 2.03/1.20  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.03/1.20  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.03/1.20  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.03/1.20  tff(c_8, plain, (![C_8, A_6, D_10, B_7]: (r1_tarski(k7_relat_1(C_8, A_6), k7_relat_1(D_10, B_7)) | ~r1_tarski(A_6, B_7) | ~r1_tarski(C_8, D_10) | ~v1_relat_1(D_10) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.20  tff(c_10, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.03/1.20  tff(c_65, plain, (![A_33, B_34]: (r1_tarski(k2_relat_1(A_33), k2_relat_1(B_34)) | ~r1_tarski(A_33, B_34) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.03/1.20  tff(c_90, plain, (![A_45, B_46, A_47]: (r1_tarski(k2_relat_1(A_45), k9_relat_1(B_46, A_47)) | ~r1_tarski(A_45, k7_relat_1(B_46, A_47)) | ~v1_relat_1(k7_relat_1(B_46, A_47)) | ~v1_relat_1(A_45) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_10, c_65])).
% 2.03/1.20  tff(c_126, plain, (![B_59, A_60, B_61, A_62]: (r1_tarski(k9_relat_1(B_59, A_60), k9_relat_1(B_61, A_62)) | ~r1_tarski(k7_relat_1(B_59, A_60), k7_relat_1(B_61, A_62)) | ~v1_relat_1(k7_relat_1(B_61, A_62)) | ~v1_relat_1(k7_relat_1(B_59, A_60)) | ~v1_relat_1(B_61) | ~v1_relat_1(B_59))), inference(superposition, [status(thm), theory('equality')], [c_10, c_90])).
% 2.03/1.20  tff(c_18, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.03/1.20  tff(c_132, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_126, c_18])).
% 2.03/1.20  tff(c_136, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_132])).
% 2.03/1.20  tff(c_137, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_136])).
% 2.03/1.20  tff(c_140, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_137])).
% 2.03/1.20  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_140])).
% 2.03/1.20  tff(c_145, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_136])).
% 2.03/1.20  tff(c_147, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_145])).
% 2.03/1.20  tff(c_150, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_147])).
% 2.03/1.20  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_20, c_150])).
% 2.03/1.20  tff(c_155, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_145])).
% 2.03/1.20  tff(c_159, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_155])).
% 2.03/1.20  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_159])).
% 2.03/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.20  
% 2.03/1.20  Inference rules
% 2.03/1.20  ----------------------
% 2.03/1.20  #Ref     : 0
% 2.03/1.20  #Sup     : 26
% 2.03/1.20  #Fact    : 0
% 2.03/1.20  #Define  : 0
% 2.03/1.20  #Split   : 3
% 2.03/1.20  #Chain   : 0
% 2.03/1.20  #Close   : 0
% 2.03/1.20  
% 2.03/1.20  Ordering : KBO
% 2.03/1.20  
% 2.03/1.20  Simplification rules
% 2.03/1.20  ----------------------
% 2.03/1.20  #Subsume      : 2
% 2.03/1.20  #Demod        : 10
% 2.03/1.20  #Tautology    : 4
% 2.03/1.20  #SimpNegUnit  : 0
% 2.03/1.20  #BackRed      : 0
% 2.03/1.20  
% 2.03/1.20  #Partial instantiations: 0
% 2.03/1.20  #Strategies tried      : 1
% 2.03/1.20  
% 2.03/1.20  Timing (in seconds)
% 2.03/1.20  ----------------------
% 2.03/1.20  Preprocessing        : 0.27
% 2.03/1.20  Parsing              : 0.15
% 2.03/1.20  CNF conversion       : 0.02
% 2.03/1.20  Main loop            : 0.18
% 2.03/1.20  Inferencing          : 0.08
% 2.03/1.20  Reduction            : 0.04
% 2.03/1.20  Demodulation         : 0.03
% 2.03/1.20  BG Simplification    : 0.01
% 2.03/1.20  Subsumption          : 0.04
% 2.03/1.20  Abstraction          : 0.01
% 2.03/1.20  MUC search           : 0.00
% 2.03/1.20  Cooper               : 0.00
% 2.03/1.20  Total                : 0.48
% 2.03/1.20  Index Insertion      : 0.00
% 2.03/1.21  Index Deletion       : 0.00
% 2.03/1.21  Index Matching       : 0.00
% 2.03/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
