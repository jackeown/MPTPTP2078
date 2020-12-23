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
% DateTime   : Thu Dec  3 10:06:55 EST 2020

% Result     : Theorem 5.20s
% Output     : CNFRefutation 5.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 (  79 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( r1_tarski(k1_relat_1(C),A)
            & r1_tarski(k2_relat_1(C),B) )
         => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_16])).

tff(c_20,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(k2_zfmisc_1(A_6,C_8),k2_zfmisc_1(B_7,C_8))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_122,plain,(
    ! [C_29,A_30,B_31] :
      ( r1_tarski(k2_zfmisc_1(C_29,A_30),k2_zfmisc_1(C_29,B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_175,plain,(
    ! [C_36,A_37,B_38] :
      ( k2_xboole_0(k2_zfmisc_1(C_36,A_37),k2_zfmisc_1(C_36,B_38)) = k2_zfmisc_1(C_36,B_38)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_209,plain,(
    ! [C_42,A_43,C_44,B_45] :
      ( r1_tarski(k2_zfmisc_1(C_42,A_43),C_44)
      | ~ r1_tarski(k2_zfmisc_1(C_42,B_45),C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_2])).

tff(c_218,plain,(
    ! [A_6,A_43,B_7,C_8] :
      ( r1_tarski(k2_zfmisc_1(A_6,A_43),k2_zfmisc_1(B_7,C_8))
      | ~ r1_tarski(A_43,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_209])).

tff(c_107,plain,(
    ! [A_25] :
      ( r1_tarski(A_25,k2_zfmisc_1(k1_relat_1(A_25),k2_relat_1(A_25)))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_327,plain,(
    ! [A_63] :
      ( k2_xboole_0(A_63,k2_zfmisc_1(k1_relat_1(A_63),k2_relat_1(A_63))) = k2_zfmisc_1(k1_relat_1(A_63),k2_relat_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_359,plain,(
    ! [A_64,C_65] :
      ( r1_tarski(A_64,C_65)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_64),k2_relat_1(A_64)),C_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_2])).

tff(c_3634,plain,(
    ! [A_208,B_209,C_210] :
      ( r1_tarski(A_208,k2_zfmisc_1(B_209,C_210))
      | ~ v1_relat_1(A_208)
      | ~ r1_tarski(k2_relat_1(A_208),C_210)
      | ~ r1_tarski(k1_relat_1(A_208),B_209) ) ),
    inference(resolution,[status(thm)],[c_218,c_359])).

tff(c_3661,plain,(
    ! [B_209] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_209,'#skF_2'))
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_209) ) ),
    inference(resolution,[status(thm)],[c_18,c_3634])).

tff(c_3678,plain,(
    ! [B_211] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_211,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3661])).

tff(c_3718,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_3678])).

tff(c_3732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_3718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.20/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/2.03  
% 5.20/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/2.03  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.20/2.03  
% 5.20/2.03  %Foreground sorts:
% 5.20/2.03  
% 5.20/2.03  
% 5.20/2.03  %Background operators:
% 5.20/2.03  
% 5.20/2.03  
% 5.20/2.03  %Foreground operators:
% 5.20/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.20/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.20/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.20/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.20/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.20/2.03  tff('#skF_1', type, '#skF_1': $i).
% 5.20/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.20/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.20/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.20/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.20/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.20/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.20/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.20/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.20/2.03  
% 5.20/2.04  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.20/2.04  tff(f_56, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.20/2.04  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 5.20/2.04  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.20/2.04  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.20/2.04  tff(f_47, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 5.20/2.04  tff(c_32, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.20/2.04  tff(c_16, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.20/2.04  tff(c_36, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_16])).
% 5.20/2.04  tff(c_20, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.20/2.04  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.20/2.04  tff(c_18, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.20/2.04  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(k2_zfmisc_1(A_6, C_8), k2_zfmisc_1(B_7, C_8)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.20/2.04  tff(c_122, plain, (![C_29, A_30, B_31]: (r1_tarski(k2_zfmisc_1(C_29, A_30), k2_zfmisc_1(C_29, B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.20/2.04  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.20/2.04  tff(c_175, plain, (![C_36, A_37, B_38]: (k2_xboole_0(k2_zfmisc_1(C_36, A_37), k2_zfmisc_1(C_36, B_38))=k2_zfmisc_1(C_36, B_38) | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_122, c_4])).
% 5.20/2.04  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.20/2.04  tff(c_209, plain, (![C_42, A_43, C_44, B_45]: (r1_tarski(k2_zfmisc_1(C_42, A_43), C_44) | ~r1_tarski(k2_zfmisc_1(C_42, B_45), C_44) | ~r1_tarski(A_43, B_45))), inference(superposition, [status(thm), theory('equality')], [c_175, c_2])).
% 5.20/2.04  tff(c_218, plain, (![A_6, A_43, B_7, C_8]: (r1_tarski(k2_zfmisc_1(A_6, A_43), k2_zfmisc_1(B_7, C_8)) | ~r1_tarski(A_43, C_8) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_8, c_209])).
% 5.20/2.04  tff(c_107, plain, (![A_25]: (r1_tarski(A_25, k2_zfmisc_1(k1_relat_1(A_25), k2_relat_1(A_25))) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.20/2.04  tff(c_327, plain, (![A_63]: (k2_xboole_0(A_63, k2_zfmisc_1(k1_relat_1(A_63), k2_relat_1(A_63)))=k2_zfmisc_1(k1_relat_1(A_63), k2_relat_1(A_63)) | ~v1_relat_1(A_63))), inference(resolution, [status(thm)], [c_107, c_4])).
% 5.20/2.04  tff(c_359, plain, (![A_64, C_65]: (r1_tarski(A_64, C_65) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_64), k2_relat_1(A_64)), C_65) | ~v1_relat_1(A_64))), inference(superposition, [status(thm), theory('equality')], [c_327, c_2])).
% 5.20/2.04  tff(c_3634, plain, (![A_208, B_209, C_210]: (r1_tarski(A_208, k2_zfmisc_1(B_209, C_210)) | ~v1_relat_1(A_208) | ~r1_tarski(k2_relat_1(A_208), C_210) | ~r1_tarski(k1_relat_1(A_208), B_209))), inference(resolution, [status(thm)], [c_218, c_359])).
% 5.20/2.04  tff(c_3661, plain, (![B_209]: (r1_tarski('#skF_3', k2_zfmisc_1(B_209, '#skF_2')) | ~v1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), B_209))), inference(resolution, [status(thm)], [c_18, c_3634])).
% 5.20/2.04  tff(c_3678, plain, (![B_211]: (r1_tarski('#skF_3', k2_zfmisc_1(B_211, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), B_211))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3661])).
% 5.20/2.04  tff(c_3718, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_3678])).
% 5.20/2.04  tff(c_3732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_3718])).
% 5.20/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/2.04  
% 5.20/2.04  Inference rules
% 5.20/2.04  ----------------------
% 5.20/2.04  #Ref     : 0
% 5.20/2.04  #Sup     : 992
% 5.20/2.04  #Fact    : 0
% 5.20/2.04  #Define  : 0
% 5.20/2.04  #Split   : 9
% 5.20/2.04  #Chain   : 0
% 5.20/2.04  #Close   : 0
% 5.20/2.04  
% 5.20/2.04  Ordering : KBO
% 5.20/2.04  
% 5.20/2.04  Simplification rules
% 5.20/2.04  ----------------------
% 5.20/2.04  #Subsume      : 235
% 5.20/2.04  #Demod        : 53
% 5.20/2.04  #Tautology    : 67
% 5.20/2.04  #SimpNegUnit  : 1
% 5.20/2.04  #BackRed      : 0
% 5.20/2.04  
% 5.20/2.04  #Partial instantiations: 0
% 5.20/2.04  #Strategies tried      : 1
% 5.20/2.04  
% 5.20/2.04  Timing (in seconds)
% 5.20/2.04  ----------------------
% 5.20/2.04  Preprocessing        : 0.27
% 5.20/2.04  Parsing              : 0.16
% 5.20/2.04  CNF conversion       : 0.02
% 5.20/2.04  Main loop            : 1.00
% 5.20/2.04  Inferencing          : 0.32
% 5.20/2.04  Reduction            : 0.26
% 5.20/2.04  Demodulation         : 0.16
% 5.20/2.04  BG Simplification    : 0.04
% 5.20/2.04  Subsumption          : 0.31
% 5.20/2.04  Abstraction          : 0.05
% 5.20/2.04  MUC search           : 0.00
% 5.20/2.04  Cooper               : 0.00
% 5.20/2.04  Total                : 1.30
% 5.20/2.04  Index Insertion      : 0.00
% 5.20/2.04  Index Deletion       : 0.00
% 5.20/2.04  Index Matching       : 0.00
% 5.20/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
