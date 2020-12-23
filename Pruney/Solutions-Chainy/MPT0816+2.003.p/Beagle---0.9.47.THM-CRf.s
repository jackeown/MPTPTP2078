%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:55 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 (  85 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( r1_tarski(k1_relat_1(C),A)
            & r1_tarski(k2_relat_1(C),B) )
         => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_23,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_27,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_23,c_16])).

tff(c_20,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_12] :
      ( r1_tarski(A_12,k2_zfmisc_1(k1_relat_1(A_12),k2_relat_1(A_12)))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r1_tarski(k2_zfmisc_1(A_6,C_8),k2_zfmisc_1(B_7,D_9))
      | ~ r1_tarski(C_8,D_9)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [C_21,B_22,A_23] :
      ( r2_hidden(C_21,B_22)
      | ~ r2_hidden(C_21,A_23)
      | ~ r1_tarski(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [A_26,B_27,B_28] :
      ( r2_hidden('#skF_1'(A_26,B_27),B_28)
      | ~ r1_tarski(A_26,B_28)
      | r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_40])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_33,B_34,B_35,B_36] :
      ( r2_hidden('#skF_1'(A_33,B_34),B_35)
      | ~ r1_tarski(B_36,B_35)
      | ~ r1_tarski(A_33,B_36)
      | r1_tarski(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_238,plain,(
    ! [A_74,B_73,B_75,A_70,C_72,D_71] :
      ( r2_hidden('#skF_1'(A_70,B_75),k2_zfmisc_1(B_73,D_71))
      | ~ r1_tarski(A_70,k2_zfmisc_1(A_74,C_72))
      | r1_tarski(A_70,B_75)
      | ~ r1_tarski(C_72,D_71)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_284,plain,(
    ! [A_80,B_81,B_82,D_83] :
      ( r2_hidden('#skF_1'(A_80,B_81),k2_zfmisc_1(B_82,D_83))
      | r1_tarski(A_80,B_81)
      | ~ r1_tarski(k2_relat_1(A_80),D_83)
      | ~ r1_tarski(k1_relat_1(A_80),B_82)
      | ~ v1_relat_1(A_80) ) ),
    inference(resolution,[status(thm)],[c_14,c_238])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_293,plain,(
    ! [A_84,B_85,D_86] :
      ( r1_tarski(A_84,k2_zfmisc_1(B_85,D_86))
      | ~ r1_tarski(k2_relat_1(A_84),D_86)
      | ~ r1_tarski(k1_relat_1(A_84),B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_284,c_4])).

tff(c_310,plain,(
    ! [B_85] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_85,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_85)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_293])).

tff(c_319,plain,(
    ! [B_87] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_87,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_310])).

tff(c_342,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_319])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:17:37 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.27  
% 2.22/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.28  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.22/1.28  
% 2.22/1.28  %Foreground sorts:
% 2.22/1.28  
% 2.22/1.28  
% 2.22/1.28  %Background operators:
% 2.22/1.28  
% 2.22/1.28  
% 2.22/1.28  %Foreground operators:
% 2.22/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.28  
% 2.22/1.29  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.22/1.29  tff(f_55, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.22/1.29  tff(f_46, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.22/1.29  tff(f_38, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 2.22/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.22/1.29  tff(c_23, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.29  tff(c_16, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.29  tff(c_27, plain, (~r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_23, c_16])).
% 2.22/1.29  tff(c_20, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.29  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.29  tff(c_18, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.29  tff(c_14, plain, (![A_12]: (r1_tarski(A_12, k2_zfmisc_1(k1_relat_1(A_12), k2_relat_1(A_12))) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.22/1.29  tff(c_8, plain, (![A_6, C_8, B_7, D_9]: (r1_tarski(k2_zfmisc_1(A_6, C_8), k2_zfmisc_1(B_7, D_9)) | ~r1_tarski(C_8, D_9) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.22/1.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.29  tff(c_40, plain, (![C_21, B_22, A_23]: (r2_hidden(C_21, B_22) | ~r2_hidden(C_21, A_23) | ~r1_tarski(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.29  tff(c_46, plain, (![A_26, B_27, B_28]: (r2_hidden('#skF_1'(A_26, B_27), B_28) | ~r1_tarski(A_26, B_28) | r1_tarski(A_26, B_27))), inference(resolution, [status(thm)], [c_6, c_40])).
% 2.22/1.29  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.29  tff(c_56, plain, (![A_33, B_34, B_35, B_36]: (r2_hidden('#skF_1'(A_33, B_34), B_35) | ~r1_tarski(B_36, B_35) | ~r1_tarski(A_33, B_36) | r1_tarski(A_33, B_34))), inference(resolution, [status(thm)], [c_46, c_2])).
% 2.22/1.29  tff(c_238, plain, (![A_74, B_73, B_75, A_70, C_72, D_71]: (r2_hidden('#skF_1'(A_70, B_75), k2_zfmisc_1(B_73, D_71)) | ~r1_tarski(A_70, k2_zfmisc_1(A_74, C_72)) | r1_tarski(A_70, B_75) | ~r1_tarski(C_72, D_71) | ~r1_tarski(A_74, B_73))), inference(resolution, [status(thm)], [c_8, c_56])).
% 2.22/1.29  tff(c_284, plain, (![A_80, B_81, B_82, D_83]: (r2_hidden('#skF_1'(A_80, B_81), k2_zfmisc_1(B_82, D_83)) | r1_tarski(A_80, B_81) | ~r1_tarski(k2_relat_1(A_80), D_83) | ~r1_tarski(k1_relat_1(A_80), B_82) | ~v1_relat_1(A_80))), inference(resolution, [status(thm)], [c_14, c_238])).
% 2.22/1.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.29  tff(c_293, plain, (![A_84, B_85, D_86]: (r1_tarski(A_84, k2_zfmisc_1(B_85, D_86)) | ~r1_tarski(k2_relat_1(A_84), D_86) | ~r1_tarski(k1_relat_1(A_84), B_85) | ~v1_relat_1(A_84))), inference(resolution, [status(thm)], [c_284, c_4])).
% 2.22/1.29  tff(c_310, plain, (![B_85]: (r1_tarski('#skF_4', k2_zfmisc_1(B_85, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), B_85) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_293])).
% 2.22/1.29  tff(c_319, plain, (![B_87]: (r1_tarski('#skF_4', k2_zfmisc_1(B_87, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), B_87))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_310])).
% 2.22/1.29  tff(c_342, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_319])).
% 2.22/1.29  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27, c_342])).
% 2.22/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.29  
% 2.22/1.29  Inference rules
% 2.22/1.29  ----------------------
% 2.22/1.29  #Ref     : 0
% 2.22/1.29  #Sup     : 78
% 2.22/1.29  #Fact    : 0
% 2.22/1.29  #Define  : 0
% 2.22/1.29  #Split   : 4
% 2.22/1.29  #Chain   : 0
% 2.22/1.29  #Close   : 0
% 2.22/1.29  
% 2.22/1.29  Ordering : KBO
% 2.22/1.29  
% 2.22/1.29  Simplification rules
% 2.22/1.29  ----------------------
% 2.22/1.29  #Subsume      : 11
% 2.22/1.29  #Demod        : 4
% 2.22/1.29  #Tautology    : 4
% 2.22/1.29  #SimpNegUnit  : 1
% 2.22/1.29  #BackRed      : 0
% 2.22/1.29  
% 2.22/1.29  #Partial instantiations: 0
% 2.22/1.29  #Strategies tried      : 1
% 2.22/1.29  
% 2.22/1.29  Timing (in seconds)
% 2.22/1.29  ----------------------
% 2.22/1.29  Preprocessing        : 0.26
% 2.22/1.29  Parsing              : 0.14
% 2.22/1.29  CNF conversion       : 0.02
% 2.22/1.29  Main loop            : 0.28
% 2.22/1.29  Inferencing          : 0.11
% 2.22/1.29  Reduction            : 0.07
% 2.22/1.29  Demodulation         : 0.05
% 2.22/1.29  BG Simplification    : 0.01
% 2.22/1.29  Subsumption          : 0.08
% 2.22/1.29  Abstraction          : 0.01
% 2.22/1.29  MUC search           : 0.00
% 2.22/1.29  Cooper               : 0.00
% 2.22/1.29  Total                : 0.56
% 2.22/1.29  Index Insertion      : 0.00
% 2.22/1.29  Index Deletion       : 0.00
% 2.22/1.29  Index Matching       : 0.00
% 2.22/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
