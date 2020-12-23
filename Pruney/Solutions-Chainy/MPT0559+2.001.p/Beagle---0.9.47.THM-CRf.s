%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:09 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 137 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   75 ( 325 expanded)
%              Number of equality atoms :    2 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(k7_relat_1(C,A),B),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_55,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k2_relat_1(A_35),k2_relat_1(B_36))
      | ~ r1_tarski(A_35,B_36)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_83,plain,(
    ! [A_47,B_48,A_49] :
      ( r1_tarski(k2_relat_1(A_47),k9_relat_1(B_48,A_49))
      | ~ r1_tarski(A_47,k7_relat_1(B_48,A_49))
      | ~ v1_relat_1(k7_relat_1(B_48,A_49))
      | ~ v1_relat_1(A_47)
      | ~ v1_relat_1(B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_55])).

tff(c_152,plain,(
    ! [B_73,A_74,B_75,A_76] :
      ( r1_tarski(k9_relat_1(B_73,A_74),k9_relat_1(B_75,A_76))
      | ~ r1_tarski(k7_relat_1(B_73,A_74),k7_relat_1(B_75,A_76))
      | ~ v1_relat_1(k7_relat_1(B_75,A_76))
      | ~ v1_relat_1(k7_relat_1(B_73,A_74))
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_83])).

tff(c_20,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_157,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_152,c_20])).

tff(c_164,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_157])).

tff(c_188,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_191,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_188])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_191])).

tff(c_197,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k7_relat_1(B_18,A_17),B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [B_9,A_8,C_11] :
      ( r1_tarski(k7_relat_1(B_9,A_8),k7_relat_1(C_11,A_8))
      | ~ r1_tarski(B_9,C_11)
      | ~ v1_relat_1(C_11)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_196,plain,
    ( ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_198,plain,(
    ~ r1_tarski(k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_201,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_198])).

tff(c_204,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_22,c_201])).

tff(c_207,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_204])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_207])).

tff(c_212,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_236,plain,(
    ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_239,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_236])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_239])).

tff(c_244,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_248,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_244])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:56:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.35  
% 2.39/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.36  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.39/1.36  
% 2.39/1.36  %Foreground sorts:
% 2.39/1.36  
% 2.39/1.36  
% 2.39/1.36  %Background operators:
% 2.39/1.36  
% 2.39/1.36  
% 2.39/1.36  %Foreground operators:
% 2.39/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.39/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.39/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.36  
% 2.39/1.37  tff(f_73, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(k7_relat_1(C, A), B), k9_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t161_relat_1)).
% 2.39/1.37  tff(f_40, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.39/1.37  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.39/1.37  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.39/1.37  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.39/1.37  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 2.39/1.37  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.39/1.37  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.39/1.37  tff(c_12, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.39/1.37  tff(c_55, plain, (![A_35, B_36]: (r1_tarski(k2_relat_1(A_35), k2_relat_1(B_36)) | ~r1_tarski(A_35, B_36) | ~v1_relat_1(B_36) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.39/1.37  tff(c_83, plain, (![A_47, B_48, A_49]: (r1_tarski(k2_relat_1(A_47), k9_relat_1(B_48, A_49)) | ~r1_tarski(A_47, k7_relat_1(B_48, A_49)) | ~v1_relat_1(k7_relat_1(B_48, A_49)) | ~v1_relat_1(A_47) | ~v1_relat_1(B_48))), inference(superposition, [status(thm), theory('equality')], [c_12, c_55])).
% 2.39/1.37  tff(c_152, plain, (![B_73, A_74, B_75, A_76]: (r1_tarski(k9_relat_1(B_73, A_74), k9_relat_1(B_75, A_76)) | ~r1_tarski(k7_relat_1(B_73, A_74), k7_relat_1(B_75, A_76)) | ~v1_relat_1(k7_relat_1(B_75, A_76)) | ~v1_relat_1(k7_relat_1(B_73, A_74)) | ~v1_relat_1(B_75) | ~v1_relat_1(B_73))), inference(superposition, [status(thm), theory('equality')], [c_12, c_83])).
% 2.39/1.37  tff(c_20, plain, (~r1_tarski(k9_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.39/1.37  tff(c_157, plain, (~r1_tarski(k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_152, c_20])).
% 2.39/1.37  tff(c_164, plain, (~r1_tarski(k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_157])).
% 2.39/1.37  tff(c_188, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_164])).
% 2.39/1.37  tff(c_191, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_188])).
% 2.39/1.37  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_191])).
% 2.39/1.37  tff(c_197, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_164])).
% 2.39/1.37  tff(c_18, plain, (![B_18, A_17]: (r1_tarski(k7_relat_1(B_18, A_17), B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.39/1.37  tff(c_10, plain, (![B_9, A_8, C_11]: (r1_tarski(k7_relat_1(B_9, A_8), k7_relat_1(C_11, A_8)) | ~r1_tarski(B_9, C_11) | ~v1_relat_1(C_11) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.39/1.37  tff(c_196, plain, (~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_164])).
% 2.39/1.37  tff(c_198, plain, (~r1_tarski(k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_196])).
% 2.39/1.37  tff(c_201, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_10, c_198])).
% 2.39/1.37  tff(c_204, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_22, c_201])).
% 2.39/1.37  tff(c_207, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_204])).
% 2.39/1.37  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_207])).
% 2.39/1.37  tff(c_212, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_196])).
% 2.39/1.37  tff(c_236, plain, (~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_212])).
% 2.39/1.37  tff(c_239, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_8, c_236])).
% 2.39/1.37  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_239])).
% 2.39/1.37  tff(c_244, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_212])).
% 2.39/1.37  tff(c_248, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_244])).
% 2.39/1.37  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_248])).
% 2.39/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.37  
% 2.39/1.37  Inference rules
% 2.39/1.37  ----------------------
% 2.39/1.37  #Ref     : 0
% 2.39/1.37  #Sup     : 51
% 2.39/1.37  #Fact    : 0
% 2.39/1.37  #Define  : 0
% 2.39/1.37  #Split   : 3
% 2.39/1.37  #Chain   : 0
% 2.39/1.37  #Close   : 0
% 2.39/1.37  
% 2.39/1.37  Ordering : KBO
% 2.39/1.37  
% 2.39/1.37  Simplification rules
% 2.39/1.37  ----------------------
% 2.39/1.37  #Subsume      : 4
% 2.39/1.37  #Demod        : 9
% 2.39/1.37  #Tautology    : 3
% 2.39/1.37  #SimpNegUnit  : 0
% 2.39/1.37  #BackRed      : 0
% 2.39/1.37  
% 2.39/1.37  #Partial instantiations: 0
% 2.39/1.37  #Strategies tried      : 1
% 2.39/1.37  
% 2.39/1.37  Timing (in seconds)
% 2.39/1.37  ----------------------
% 2.59/1.37  Preprocessing        : 0.30
% 2.59/1.37  Parsing              : 0.17
% 2.59/1.37  CNF conversion       : 0.02
% 2.59/1.37  Main loop            : 0.27
% 2.59/1.37  Inferencing          : 0.11
% 2.59/1.37  Reduction            : 0.06
% 2.59/1.37  Demodulation         : 0.04
% 2.59/1.37  BG Simplification    : 0.01
% 2.59/1.37  Subsumption          : 0.06
% 2.59/1.37  Abstraction          : 0.01
% 2.59/1.37  MUC search           : 0.00
% 2.59/1.37  Cooper               : 0.00
% 2.59/1.37  Total                : 0.59
% 2.59/1.37  Index Insertion      : 0.00
% 2.59/1.37  Index Deletion       : 0.00
% 2.59/1.37  Index Matching       : 0.00
% 2.59/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
