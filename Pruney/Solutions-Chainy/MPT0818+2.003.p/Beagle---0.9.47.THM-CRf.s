%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:57 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 (  78 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_tarski(k2_relat_1(D),B)
         => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_41,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_27,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_31,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_27])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_155,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(k1_relat_1(A_57),k1_relat_1(B_58))
      | ~ r1_tarski(A_57,B_58)
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_8,B_9)),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,C_37)
      | ~ r1_tarski(B_38,C_37)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_36,A_8,B_9] :
      ( r1_tarski(A_36,A_8)
      | ~ r1_tarski(A_36,k1_relat_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_163,plain,(
    ! [A_57,A_8,B_9] :
      ( r1_tarski(k1_relat_1(A_57),A_8)
      | ~ r1_tarski(A_57,k2_zfmisc_1(A_8,B_9))
      | ~ v1_relat_1(k2_zfmisc_1(A_8,B_9))
      | ~ v1_relat_1(A_57) ) ),
    inference(resolution,[status(thm)],[c_155,c_71])).

tff(c_212,plain,(
    ! [A_67,A_68,B_69] :
      ( r1_tarski(k1_relat_1(A_67),A_68)
      | ~ r1_tarski(A_67,k2_zfmisc_1(A_68,B_69))
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_163])).

tff(c_219,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_31,c_212])).

tff(c_229,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_219])).

tff(c_22,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_257,plain,(
    ! [C_71,A_72,B_73] :
      ( m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ r1_tarski(k2_relat_1(C_71),B_73)
      | ~ r1_tarski(k1_relat_1(C_71),A_72)
      | ~ v1_relat_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_266,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_257,c_20])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_229,c_22,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.31  
% 2.14/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.31  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.14/1.31  
% 2.14/1.31  %Foreground sorts:
% 2.14/1.31  
% 2.14/1.31  
% 2.14/1.31  %Background operators:
% 2.14/1.31  
% 2.14/1.31  
% 2.14/1.31  %Foreground operators:
% 2.14/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.31  
% 2.35/1.32  tff(f_69, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 2.35/1.32  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.35/1.32  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.35/1.32  tff(f_37, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.35/1.32  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.35/1.32  tff(f_39, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 2.35/1.32  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.35/1.32  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.35/1.32  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.35/1.32  tff(c_41, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.35/1.32  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_41])).
% 2.35/1.32  tff(c_27, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.32  tff(c_31, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_27])).
% 2.35/1.32  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.35/1.32  tff(c_155, plain, (![A_57, B_58]: (r1_tarski(k1_relat_1(A_57), k1_relat_1(B_58)) | ~r1_tarski(A_57, B_58) | ~v1_relat_1(B_58) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.35/1.32  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_8, B_9)), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.35/1.32  tff(c_63, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, C_37) | ~r1_tarski(B_38, C_37) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.32  tff(c_71, plain, (![A_36, A_8, B_9]: (r1_tarski(A_36, A_8) | ~r1_tarski(A_36, k1_relat_1(k2_zfmisc_1(A_8, B_9))))), inference(resolution, [status(thm)], [c_10, c_63])).
% 2.35/1.32  tff(c_163, plain, (![A_57, A_8, B_9]: (r1_tarski(k1_relat_1(A_57), A_8) | ~r1_tarski(A_57, k2_zfmisc_1(A_8, B_9)) | ~v1_relat_1(k2_zfmisc_1(A_8, B_9)) | ~v1_relat_1(A_57))), inference(resolution, [status(thm)], [c_155, c_71])).
% 2.35/1.32  tff(c_212, plain, (![A_67, A_68, B_69]: (r1_tarski(k1_relat_1(A_67), A_68) | ~r1_tarski(A_67, k2_zfmisc_1(A_68, B_69)) | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_163])).
% 2.35/1.32  tff(c_219, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_31, c_212])).
% 2.35/1.32  tff(c_229, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_219])).
% 2.35/1.32  tff(c_22, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.35/1.32  tff(c_257, plain, (![C_71, A_72, B_73]: (m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~r1_tarski(k2_relat_1(C_71), B_73) | ~r1_tarski(k1_relat_1(C_71), A_72) | ~v1_relat_1(C_71))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.35/1.32  tff(c_20, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.35/1.32  tff(c_266, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_257, c_20])).
% 2.35/1.32  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_229, c_22, c_266])).
% 2.35/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.32  
% 2.35/1.32  Inference rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Ref     : 0
% 2.35/1.33  #Sup     : 52
% 2.35/1.33  #Fact    : 0
% 2.35/1.33  #Define  : 0
% 2.35/1.33  #Split   : 1
% 2.35/1.33  #Chain   : 0
% 2.35/1.33  #Close   : 0
% 2.35/1.33  
% 2.35/1.33  Ordering : KBO
% 2.35/1.33  
% 2.35/1.33  Simplification rules
% 2.35/1.33  ----------------------
% 2.35/1.33  #Subsume      : 1
% 2.35/1.33  #Demod        : 13
% 2.35/1.33  #Tautology    : 5
% 2.35/1.33  #SimpNegUnit  : 0
% 2.35/1.33  #BackRed      : 0
% 2.35/1.33  
% 2.35/1.33  #Partial instantiations: 0
% 2.35/1.33  #Strategies tried      : 1
% 2.35/1.33  
% 2.35/1.33  Timing (in seconds)
% 2.35/1.33  ----------------------
% 2.35/1.33  Preprocessing        : 0.26
% 2.35/1.33  Parsing              : 0.14
% 2.35/1.33  CNF conversion       : 0.02
% 2.35/1.33  Main loop            : 0.24
% 2.35/1.33  Inferencing          : 0.09
% 2.35/1.33  Reduction            : 0.07
% 2.35/1.33  Demodulation         : 0.05
% 2.35/1.33  BG Simplification    : 0.01
% 2.35/1.33  Subsumption          : 0.05
% 2.35/1.33  Abstraction          : 0.01
% 2.35/1.33  MUC search           : 0.00
% 2.35/1.33  Cooper               : 0.00
% 2.35/1.33  Total                : 0.53
% 2.35/1.33  Index Insertion      : 0.00
% 2.35/1.33  Index Deletion       : 0.00
% 2.35/1.33  Index Matching       : 0.00
% 2.35/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
