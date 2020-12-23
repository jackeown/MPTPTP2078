%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:05 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 101 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 239 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(B,C)
             => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_64,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ! [B_24,A_25] :
      ( v1_relat_1(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_25))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_37,plain,(
    ! [A_26,B_27] :
      ( v1_relat_1(A_26)
      | ~ v1_relat_1(B_27)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_4,c_32])).

tff(c_44,plain,(
    ! [B_16,A_15] :
      ( v1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_37])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [B_7,A_6,C_9] :
      ( r1_tarski(k7_relat_1(B_7,A_6),k7_relat_1(C_9,A_6))
      | ~ r1_tarski(B_7,C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k2_relat_1(A_34),k2_relat_1(B_35))
      | ~ r1_tarski(A_34,B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_83,plain,(
    ! [A_43,B_44,A_45] :
      ( r1_tarski(k2_relat_1(A_43),k9_relat_1(B_44,A_45))
      | ~ r1_tarski(A_43,k7_relat_1(B_44,A_45))
      | ~ v1_relat_1(k7_relat_1(B_44,A_45))
      | ~ v1_relat_1(A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_63])).

tff(c_137,plain,(
    ! [B_66,A_67,B_68,A_69] :
      ( r1_tarski(k9_relat_1(B_66,A_67),k9_relat_1(B_68,A_69))
      | ~ r1_tarski(k7_relat_1(B_66,A_67),k7_relat_1(B_68,A_69))
      | ~ v1_relat_1(k7_relat_1(B_68,A_69))
      | ~ v1_relat_1(k7_relat_1(B_66,A_67))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_83])).

tff(c_18,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_143,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_137,c_18])).

tff(c_147,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_143])).

tff(c_148,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_151,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_148])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_151])).

tff(c_156,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_158,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_161,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_158])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_161])).

tff(c_166,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_170,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_166])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:03:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.21  
% 2.02/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.21  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.02/1.21  
% 2.02/1.21  %Foreground sorts:
% 2.02/1.21  
% 2.02/1.21  
% 2.02/1.21  %Background operators:
% 2.02/1.21  
% 2.02/1.21  
% 2.02/1.21  %Foreground operators:
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.02/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.02/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.21  
% 2.17/1.22  tff(f_74, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 2.17/1.22  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.17/1.22  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.17/1.22  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.22  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 2.17/1.22  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.17/1.22  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.17/1.22  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.17/1.22  tff(c_16, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.17/1.22  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.22  tff(c_32, plain, (![B_24, A_25]: (v1_relat_1(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_25)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.17/1.22  tff(c_37, plain, (![A_26, B_27]: (v1_relat_1(A_26) | ~v1_relat_1(B_27) | ~r1_tarski(A_26, B_27))), inference(resolution, [status(thm)], [c_4, c_32])).
% 2.17/1.22  tff(c_44, plain, (![B_16, A_15]: (v1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_16, c_37])).
% 2.17/1.22  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.17/1.22  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.17/1.22  tff(c_8, plain, (![B_7, A_6, C_9]: (r1_tarski(k7_relat_1(B_7, A_6), k7_relat_1(C_9, A_6)) | ~r1_tarski(B_7, C_9) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.22  tff(c_10, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.22  tff(c_63, plain, (![A_34, B_35]: (r1_tarski(k2_relat_1(A_34), k2_relat_1(B_35)) | ~r1_tarski(A_34, B_35) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.17/1.22  tff(c_83, plain, (![A_43, B_44, A_45]: (r1_tarski(k2_relat_1(A_43), k9_relat_1(B_44, A_45)) | ~r1_tarski(A_43, k7_relat_1(B_44, A_45)) | ~v1_relat_1(k7_relat_1(B_44, A_45)) | ~v1_relat_1(A_43) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_10, c_63])).
% 2.17/1.22  tff(c_137, plain, (![B_66, A_67, B_68, A_69]: (r1_tarski(k9_relat_1(B_66, A_67), k9_relat_1(B_68, A_69)) | ~r1_tarski(k7_relat_1(B_66, A_67), k7_relat_1(B_68, A_69)) | ~v1_relat_1(k7_relat_1(B_68, A_69)) | ~v1_relat_1(k7_relat_1(B_66, A_67)) | ~v1_relat_1(B_68) | ~v1_relat_1(B_66))), inference(superposition, [status(thm), theory('equality')], [c_10, c_83])).
% 2.17/1.22  tff(c_18, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.17/1.22  tff(c_143, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_137, c_18])).
% 2.17/1.22  tff(c_147, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_143])).
% 2.17/1.22  tff(c_148, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_147])).
% 2.17/1.22  tff(c_151, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_148])).
% 2.17/1.22  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_151])).
% 2.17/1.22  tff(c_156, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_147])).
% 2.17/1.22  tff(c_158, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_156])).
% 2.17/1.22  tff(c_161, plain, (~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_158])).
% 2.17/1.22  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_161])).
% 2.17/1.22  tff(c_166, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_156])).
% 2.17/1.22  tff(c_170, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_166])).
% 2.17/1.22  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_170])).
% 2.17/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.22  
% 2.17/1.22  Inference rules
% 2.17/1.22  ----------------------
% 2.17/1.22  #Ref     : 0
% 2.17/1.22  #Sup     : 30
% 2.17/1.22  #Fact    : 0
% 2.17/1.22  #Define  : 0
% 2.17/1.22  #Split   : 2
% 2.17/1.22  #Chain   : 0
% 2.17/1.22  #Close   : 0
% 2.17/1.22  
% 2.17/1.22  Ordering : KBO
% 2.17/1.22  
% 2.17/1.22  Simplification rules
% 2.17/1.22  ----------------------
% 2.17/1.22  #Subsume      : 2
% 2.17/1.22  #Demod        : 9
% 2.17/1.22  #Tautology    : 4
% 2.17/1.22  #SimpNegUnit  : 0
% 2.17/1.22  #BackRed      : 0
% 2.17/1.22  
% 2.17/1.22  #Partial instantiations: 0
% 2.17/1.22  #Strategies tried      : 1
% 2.17/1.22  
% 2.17/1.22  Timing (in seconds)
% 2.17/1.22  ----------------------
% 2.17/1.22  Preprocessing        : 0.26
% 2.17/1.22  Parsing              : 0.15
% 2.17/1.22  CNF conversion       : 0.02
% 2.17/1.22  Main loop            : 0.20
% 2.17/1.22  Inferencing          : 0.09
% 2.17/1.22  Reduction            : 0.04
% 2.17/1.22  Demodulation         : 0.03
% 2.17/1.22  BG Simplification    : 0.01
% 2.17/1.22  Subsumption          : 0.05
% 2.17/1.22  Abstraction          : 0.01
% 2.17/1.22  MUC search           : 0.00
% 2.17/1.22  Cooper               : 0.00
% 2.17/1.22  Total                : 0.50
% 2.17/1.22  Index Insertion      : 0.00
% 2.17/1.22  Index Deletion       : 0.00
% 2.17/1.22  Index Matching       : 0.00
% 2.17/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
