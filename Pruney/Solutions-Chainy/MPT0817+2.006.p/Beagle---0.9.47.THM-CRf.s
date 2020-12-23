%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:56 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  90 expanded)
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

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( r1_tarski(k1_relat_1(D),B)
         => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_41,plain,(
    ! [B_27,A_28] :
      ( v1_relat_1(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_51,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_47])).

tff(c_22,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_27,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_31,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_27])).

tff(c_151,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k2_relat_1(A_51),k2_relat_1(B_52))
      | ~ r1_tarski(A_51,B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_11,B_12)),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_tarski(A_33,C_34)
      | ~ r1_tarski(B_35,C_34)
      | ~ r1_tarski(A_33,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_33,B_12,A_11] :
      ( r1_tarski(A_33,B_12)
      | ~ r1_tarski(A_33,k2_relat_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_155,plain,(
    ! [A_51,B_12,A_11] :
      ( r1_tarski(k2_relat_1(A_51),B_12)
      | ~ r1_tarski(A_51,k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_151,c_77])).

tff(c_210,plain,(
    ! [A_60,B_61,A_62] :
      ( r1_tarski(k2_relat_1(A_60),B_61)
      | ~ r1_tarski(A_60,k2_zfmisc_1(A_62,B_61))
      | ~ v1_relat_1(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_155])).

tff(c_217,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_31,c_210])).

tff(c_225,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_217])).

tff(c_319,plain,(
    ! [C_71,A_72,B_73] :
      ( m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ r1_tarski(k2_relat_1(C_71),B_73)
      | ~ r1_tarski(k1_relat_1(C_71),A_72)
      | ~ v1_relat_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_328,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_319,c_20])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_22,c_225,c_328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:56:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.30  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.30  
% 2.17/1.30  %Foreground sorts:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Background operators:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Foreground operators:
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.30  
% 2.17/1.31  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.17/1.31  tff(f_72, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.17/1.31  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.31  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.17/1.31  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.17/1.31  tff(f_46, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 2.17/1.31  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.17/1.31  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.17/1.31  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.31  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.17/1.31  tff(c_41, plain, (![B_27, A_28]: (v1_relat_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.31  tff(c_47, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_41])).
% 2.17/1.31  tff(c_51, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_47])).
% 2.17/1.31  tff(c_22, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.17/1.31  tff(c_27, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.31  tff(c_31, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_27])).
% 2.17/1.31  tff(c_151, plain, (![A_51, B_52]: (r1_tarski(k2_relat_1(A_51), k2_relat_1(B_52)) | ~r1_tarski(A_51, B_52) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.31  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_11, B_12)), B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.31  tff(c_69, plain, (![A_33, C_34, B_35]: (r1_tarski(A_33, C_34) | ~r1_tarski(B_35, C_34) | ~r1_tarski(A_33, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.31  tff(c_77, plain, (![A_33, B_12, A_11]: (r1_tarski(A_33, B_12) | ~r1_tarski(A_33, k2_relat_1(k2_zfmisc_1(A_11, B_12))))), inference(resolution, [status(thm)], [c_12, c_69])).
% 2.17/1.31  tff(c_155, plain, (![A_51, B_12, A_11]: (r1_tarski(k2_relat_1(A_51), B_12) | ~r1_tarski(A_51, k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_151, c_77])).
% 2.17/1.31  tff(c_210, plain, (![A_60, B_61, A_62]: (r1_tarski(k2_relat_1(A_60), B_61) | ~r1_tarski(A_60, k2_zfmisc_1(A_62, B_61)) | ~v1_relat_1(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_155])).
% 2.17/1.31  tff(c_217, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_31, c_210])).
% 2.17/1.31  tff(c_225, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_217])).
% 2.17/1.31  tff(c_319, plain, (![C_71, A_72, B_73]: (m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~r1_tarski(k2_relat_1(C_71), B_73) | ~r1_tarski(k1_relat_1(C_71), A_72) | ~v1_relat_1(C_71))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.17/1.31  tff(c_20, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.17/1.31  tff(c_328, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_319, c_20])).
% 2.17/1.31  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_22, c_225, c_328])).
% 2.17/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  Inference rules
% 2.17/1.31  ----------------------
% 2.17/1.31  #Ref     : 0
% 2.17/1.31  #Sup     : 68
% 2.17/1.31  #Fact    : 0
% 2.17/1.31  #Define  : 0
% 2.17/1.31  #Split   : 4
% 2.17/1.31  #Chain   : 0
% 2.17/1.31  #Close   : 0
% 2.17/1.31  
% 2.17/1.31  Ordering : KBO
% 2.17/1.31  
% 2.17/1.31  Simplification rules
% 2.17/1.31  ----------------------
% 2.17/1.31  #Subsume      : 10
% 2.17/1.31  #Demod        : 15
% 2.17/1.31  #Tautology    : 5
% 2.17/1.31  #SimpNegUnit  : 0
% 2.17/1.31  #BackRed      : 0
% 2.17/1.31  
% 2.17/1.31  #Partial instantiations: 0
% 2.17/1.31  #Strategies tried      : 1
% 2.17/1.31  
% 2.17/1.31  Timing (in seconds)
% 2.17/1.31  ----------------------
% 2.17/1.31  Preprocessing        : 0.27
% 2.17/1.31  Parsing              : 0.16
% 2.17/1.31  CNF conversion       : 0.02
% 2.17/1.31  Main loop            : 0.26
% 2.17/1.31  Inferencing          : 0.10
% 2.17/1.31  Reduction            : 0.08
% 2.17/1.31  Demodulation         : 0.06
% 2.17/1.31  BG Simplification    : 0.01
% 2.17/1.31  Subsumption          : 0.05
% 2.17/1.31  Abstraction          : 0.01
% 2.17/1.31  MUC search           : 0.00
% 2.17/1.31  Cooper               : 0.00
% 2.17/1.31  Total                : 0.56
% 2.17/1.31  Index Insertion      : 0.00
% 2.17/1.31  Index Deletion       : 0.00
% 2.17/1.31  Index Matching       : 0.00
% 2.17/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
