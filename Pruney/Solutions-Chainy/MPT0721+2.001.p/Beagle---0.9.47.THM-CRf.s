%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:52 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  76 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v5_relat_1(C,A)
          & v1_funct_1(C) )
       => ( r2_hidden(B,k1_relat_1(C))
         => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_22,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [B_26,C_27,A_28] :
      ( r2_hidden(k1_funct_1(B_26,C_27),A_28)
      | ~ r2_hidden(C_27,k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v5_relat_1(B_26,A_28)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [A_19,C_20,B_21] :
      ( m1_subset_1(A_19,C_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_19,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_43,plain,(
    ! [A_19,B_4,A_3] :
      ( m1_subset_1(A_19,B_4)
      | ~ r2_hidden(A_19,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_40])).

tff(c_58,plain,(
    ! [B_29,C_30,B_31,A_32] :
      ( m1_subset_1(k1_funct_1(B_29,C_30),B_31)
      | ~ r1_tarski(A_32,B_31)
      | ~ r2_hidden(C_30,k1_relat_1(B_29))
      | ~ v1_funct_1(B_29)
      | ~ v5_relat_1(B_29,A_32)
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_54,c_43])).

tff(c_62,plain,(
    ! [B_33,C_34,B_35] :
      ( m1_subset_1(k1_funct_1(B_33,C_34),B_35)
      | ~ r2_hidden(C_34,k1_relat_1(B_33))
      | ~ v1_funct_1(B_33)
      | ~ v5_relat_1(B_33,B_35)
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_67,plain,(
    ! [B_35] :
      ( m1_subset_1(k1_funct_1('#skF_3','#skF_2'),B_35)
      | ~ v1_funct_1('#skF_3')
      | ~ v5_relat_1('#skF_3',B_35)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_62])).

tff(c_72,plain,(
    ! [B_36] :
      ( m1_subset_1(k1_funct_1('#skF_3','#skF_2'),B_36)
      | ~ v5_relat_1('#skF_3',B_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_67])).

tff(c_16,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_3','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_82,plain,(
    ~ v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_16])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.12  
% 1.76/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.13  %$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.76/1.13  
% 1.76/1.13  %Foreground sorts:
% 1.76/1.13  
% 1.76/1.13  
% 1.76/1.13  %Background operators:
% 1.76/1.13  
% 1.76/1.13  
% 1.76/1.13  %Foreground operators:
% 1.76/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.76/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.76/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.76/1.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.76/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.76/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.76/1.13  
% 1.80/1.14  tff(f_63, negated_conjecture, ~(![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 1.80/1.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.80/1.14  tff(f_52, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 1.80/1.14  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.80/1.14  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 1.80/1.14  tff(c_22, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.80/1.14  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.80/1.14  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.80/1.14  tff(c_18, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.80/1.14  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.14  tff(c_54, plain, (![B_26, C_27, A_28]: (r2_hidden(k1_funct_1(B_26, C_27), A_28) | ~r2_hidden(C_27, k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v5_relat_1(B_26, A_28) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.80/1.14  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.14  tff(c_40, plain, (![A_19, C_20, B_21]: (m1_subset_1(A_19, C_20) | ~m1_subset_1(B_21, k1_zfmisc_1(C_20)) | ~r2_hidden(A_19, B_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.80/1.14  tff(c_43, plain, (![A_19, B_4, A_3]: (m1_subset_1(A_19, B_4) | ~r2_hidden(A_19, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_10, c_40])).
% 1.80/1.14  tff(c_58, plain, (![B_29, C_30, B_31, A_32]: (m1_subset_1(k1_funct_1(B_29, C_30), B_31) | ~r1_tarski(A_32, B_31) | ~r2_hidden(C_30, k1_relat_1(B_29)) | ~v1_funct_1(B_29) | ~v5_relat_1(B_29, A_32) | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_54, c_43])).
% 1.80/1.14  tff(c_62, plain, (![B_33, C_34, B_35]: (m1_subset_1(k1_funct_1(B_33, C_34), B_35) | ~r2_hidden(C_34, k1_relat_1(B_33)) | ~v1_funct_1(B_33) | ~v5_relat_1(B_33, B_35) | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_6, c_58])).
% 1.80/1.14  tff(c_67, plain, (![B_35]: (m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), B_35) | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', B_35) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_62])).
% 1.80/1.14  tff(c_72, plain, (![B_36]: (m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), B_36) | ~v5_relat_1('#skF_3', B_36))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_67])).
% 1.80/1.14  tff(c_16, plain, (~m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.80/1.14  tff(c_82, plain, (~v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_16])).
% 1.80/1.14  tff(c_88, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_82])).
% 1.80/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.14  
% 1.80/1.14  Inference rules
% 1.80/1.14  ----------------------
% 1.80/1.14  #Ref     : 0
% 1.80/1.14  #Sup     : 12
% 1.80/1.14  #Fact    : 0
% 1.80/1.14  #Define  : 0
% 1.80/1.14  #Split   : 0
% 1.80/1.14  #Chain   : 0
% 1.80/1.14  #Close   : 0
% 1.80/1.14  
% 1.80/1.14  Ordering : KBO
% 1.80/1.14  
% 1.80/1.14  Simplification rules
% 1.80/1.14  ----------------------
% 1.80/1.14  #Subsume      : 0
% 1.80/1.14  #Demod        : 5
% 1.80/1.14  #Tautology    : 3
% 1.80/1.14  #SimpNegUnit  : 0
% 1.80/1.14  #BackRed      : 0
% 1.80/1.14  
% 1.80/1.14  #Partial instantiations: 0
% 1.80/1.14  #Strategies tried      : 1
% 1.80/1.14  
% 1.80/1.14  Timing (in seconds)
% 1.80/1.14  ----------------------
% 1.80/1.14  Preprocessing        : 0.27
% 1.80/1.14  Parsing              : 0.15
% 1.80/1.14  CNF conversion       : 0.02
% 1.80/1.14  Main loop            : 0.12
% 1.80/1.14  Inferencing          : 0.05
% 1.80/1.14  Reduction            : 0.03
% 1.80/1.14  Demodulation         : 0.02
% 1.80/1.14  BG Simplification    : 0.01
% 1.80/1.14  Subsumption          : 0.02
% 1.80/1.14  Abstraction          : 0.00
% 1.80/1.14  MUC search           : 0.00
% 1.80/1.14  Cooper               : 0.00
% 1.80/1.14  Total                : 0.42
% 1.80/1.14  Index Insertion      : 0.00
% 1.80/1.14  Index Deletion       : 0.00
% 1.80/1.14  Index Matching       : 0.00
% 1.80/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
