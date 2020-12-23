%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:01 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   45 (  75 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 ( 114 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_23,plain,(
    ! [C_16,A_17,B_18] :
      ( v1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_27,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_23])).

tff(c_35,plain,(
    ! [C_26,B_27,A_28] :
      ( v5_relat_1(C_26,B_27)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_28,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_39,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_35])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [C_23,A_24,B_25] :
      ( v4_relat_1(C_23,A_24)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_30])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v4_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_9] :
      ( k2_xboole_0(k1_relat_1(A_9),k2_relat_1(A_9)) = k3_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_59,plain,(
    ! [A_34,C_35,B_36,D_37] :
      ( r1_tarski(k2_xboole_0(A_34,C_35),k2_xboole_0(B_36,D_37))
      | ~ r1_tarski(C_35,D_37)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_38,B_39,D_40] :
      ( r1_tarski(k3_relat_1(A_38),k2_xboole_0(B_39,D_40))
      | ~ r1_tarski(k2_relat_1(A_38),D_40)
      | ~ r1_tarski(k1_relat_1(A_38),B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_59])).

tff(c_20,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_69,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_20])).

tff(c_75,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_69])).

tff(c_80,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_83,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_34,c_83])).

tff(c_88,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_92,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_88])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_39,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:43:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.16  
% 1.81/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.16  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.81/1.16  
% 1.81/1.16  %Foreground sorts:
% 1.81/1.16  
% 1.81/1.16  
% 1.81/1.16  %Background operators:
% 1.81/1.16  
% 1.81/1.16  
% 1.81/1.16  %Foreground operators:
% 1.81/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.16  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.81/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.81/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.81/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.81/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.81/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.16  
% 1.81/1.17  tff(f_62, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 1.81/1.17  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.81/1.17  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.81/1.17  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.81/1.17  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 1.81/1.17  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.81/1.17  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 1.81/1.17  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.81/1.17  tff(c_23, plain, (![C_16, A_17, B_18]: (v1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.81/1.17  tff(c_27, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_23])).
% 1.81/1.17  tff(c_35, plain, (![C_26, B_27, A_28]: (v5_relat_1(C_26, B_27) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_28, B_27))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.17  tff(c_39, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_35])).
% 1.81/1.17  tff(c_10, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.17  tff(c_30, plain, (![C_23, A_24, B_25]: (v4_relat_1(C_23, A_24) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.17  tff(c_34, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_30])).
% 1.81/1.17  tff(c_6, plain, (![B_6, A_5]: (r1_tarski(k1_relat_1(B_6), A_5) | ~v4_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.81/1.17  tff(c_12, plain, (![A_9]: (k2_xboole_0(k1_relat_1(A_9), k2_relat_1(A_9))=k3_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.81/1.17  tff(c_59, plain, (![A_34, C_35, B_36, D_37]: (r1_tarski(k2_xboole_0(A_34, C_35), k2_xboole_0(B_36, D_37)) | ~r1_tarski(C_35, D_37) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.17  tff(c_66, plain, (![A_38, B_39, D_40]: (r1_tarski(k3_relat_1(A_38), k2_xboole_0(B_39, D_40)) | ~r1_tarski(k2_relat_1(A_38), D_40) | ~r1_tarski(k1_relat_1(A_38), B_39) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_12, c_59])).
% 1.81/1.17  tff(c_20, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.81/1.17  tff(c_69, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_20])).
% 1.81/1.17  tff(c_75, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_27, c_69])).
% 1.81/1.17  tff(c_80, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_75])).
% 1.81/1.17  tff(c_83, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_80])).
% 1.81/1.17  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27, c_34, c_83])).
% 1.81/1.17  tff(c_88, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_75])).
% 1.81/1.17  tff(c_92, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_88])).
% 1.81/1.17  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27, c_39, c_92])).
% 1.81/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.17  
% 1.81/1.17  Inference rules
% 1.81/1.17  ----------------------
% 1.81/1.17  #Ref     : 0
% 1.81/1.17  #Sup     : 14
% 1.81/1.17  #Fact    : 0
% 1.81/1.17  #Define  : 0
% 1.81/1.17  #Split   : 1
% 1.81/1.17  #Chain   : 0
% 1.81/1.17  #Close   : 0
% 1.81/1.17  
% 1.81/1.17  Ordering : KBO
% 1.81/1.17  
% 1.81/1.17  Simplification rules
% 1.81/1.17  ----------------------
% 1.81/1.17  #Subsume      : 0
% 1.81/1.17  #Demod        : 5
% 1.81/1.17  #Tautology    : 4
% 1.81/1.17  #SimpNegUnit  : 0
% 1.81/1.17  #BackRed      : 0
% 1.81/1.17  
% 1.81/1.17  #Partial instantiations: 0
% 1.81/1.17  #Strategies tried      : 1
% 1.81/1.17  
% 1.81/1.17  Timing (in seconds)
% 1.81/1.17  ----------------------
% 1.81/1.17  Preprocessing        : 0.28
% 1.81/1.17  Parsing              : 0.15
% 1.81/1.17  CNF conversion       : 0.02
% 1.81/1.17  Main loop            : 0.13
% 1.81/1.17  Inferencing          : 0.06
% 1.81/1.17  Reduction            : 0.03
% 1.81/1.17  Demodulation         : 0.02
% 1.81/1.17  BG Simplification    : 0.01
% 1.81/1.17  Subsumption          : 0.02
% 1.81/1.18  Abstraction          : 0.00
% 1.81/1.18  MUC search           : 0.00
% 1.81/1.18  Cooper               : 0.00
% 1.81/1.18  Total                : 0.43
% 1.81/1.18  Index Insertion      : 0.00
% 1.81/1.18  Index Deletion       : 0.00
% 1.81/1.18  Index Matching       : 0.00
% 1.81/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
