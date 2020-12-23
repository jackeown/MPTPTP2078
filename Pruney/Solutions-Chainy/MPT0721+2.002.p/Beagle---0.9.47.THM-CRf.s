%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:52 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   57 (  86 expanded)
%              Number of leaves         :   24 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 208 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v5_relat_1(C,A)
          & v1_funct_1(C) )
       => ( r2_hidden(B,k1_relat_1(C))
         => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_34,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_45,plain,(
    ! [B_19,A_20] :
      ( m1_subset_1(B_19,A_20)
      | ~ v1_xboole_0(B_19)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_49,plain,
    ( ~ v1_xboole_0(k1_funct_1('#skF_5','#skF_4'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_45,c_26])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_32,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_138,plain,(
    ! [B_45,A_46] :
      ( r2_hidden(k1_funct_1(B_45,A_46),k2_relat_1(B_45))
      | ~ r2_hidden(A_46,k1_relat_1(B_45))
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_475,plain,(
    ! [B_109,A_110,B_111] :
      ( r2_hidden(k1_funct_1(B_109,A_110),B_111)
      | ~ r1_tarski(k2_relat_1(B_109),B_111)
      | ~ r2_hidden(A_110,k1_relat_1(B_109))
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_138,c_6])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(B_11,A_10)
      | ~ r2_hidden(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_587,plain,(
    ! [B_131,A_132,B_133] :
      ( m1_subset_1(k1_funct_1(B_131,A_132),B_133)
      | v1_xboole_0(B_133)
      | ~ r1_tarski(k2_relat_1(B_131),B_133)
      | ~ r2_hidden(A_132,k1_relat_1(B_131))
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(resolution,[status(thm)],[c_475,c_12])).

tff(c_657,plain,(
    ! [B_147,A_148,A_149] :
      ( m1_subset_1(k1_funct_1(B_147,A_148),A_149)
      | v1_xboole_0(A_149)
      | ~ r2_hidden(A_148,k1_relat_1(B_147))
      | ~ v1_funct_1(B_147)
      | ~ v5_relat_1(B_147,A_149)
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_22,c_587])).

tff(c_683,plain,(
    ! [A_149] :
      ( m1_subset_1(k1_funct_1('#skF_5','#skF_4'),A_149)
      | v1_xboole_0(A_149)
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_149)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_657])).

tff(c_695,plain,(
    ! [A_150] :
      ( m1_subset_1(k1_funct_1('#skF_5','#skF_4'),A_150)
      | v1_xboole_0(A_150)
      | ~ v5_relat_1('#skF_5',A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_683])).

tff(c_704,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_695,c_26])).

tff(c_709,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_704])).

tff(c_711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_709])).

tff(c_713,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_771,plain,(
    ! [C_167,B_168,A_169] :
      ( r2_hidden(C_167,B_168)
      | ~ r2_hidden(C_167,A_169)
      | ~ r1_tarski(A_169,B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_813,plain,(
    ! [A_176,B_177] :
      ( r2_hidden('#skF_1'(A_176),B_177)
      | ~ r1_tarski(A_176,B_177)
      | v1_xboole_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_4,c_771])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_825,plain,(
    ! [B_178,A_179] :
      ( ~ v1_xboole_0(B_178)
      | ~ r1_tarski(A_179,B_178)
      | v1_xboole_0(A_179) ) ),
    inference(resolution,[status(thm)],[c_813,c_2])).

tff(c_867,plain,(
    ! [A_186,B_187] :
      ( ~ v1_xboole_0(A_186)
      | v1_xboole_0(k2_relat_1(B_187))
      | ~ v5_relat_1(B_187,A_186)
      | ~ v1_relat_1(B_187) ) ),
    inference(resolution,[status(thm)],[c_22,c_825])).

tff(c_871,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_867])).

tff(c_875,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_713,c_871])).

tff(c_844,plain,(
    ! [B_182,A_183] :
      ( r2_hidden(k1_funct_1(B_182,A_183),k2_relat_1(B_182))
      | ~ r2_hidden(A_183,k1_relat_1(B_182))
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_925,plain,(
    ! [B_198,A_199] :
      ( ~ v1_xboole_0(k2_relat_1(B_198))
      | ~ r2_hidden(A_199,k1_relat_1(B_198))
      | ~ v1_funct_1(B_198)
      | ~ v1_relat_1(B_198) ) ),
    inference(resolution,[status(thm)],[c_844,c_2])).

tff(c_948,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_925])).

tff(c_957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_875,c_948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:44:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.51  
% 3.13/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.52  %$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.13/1.52  
% 3.13/1.52  %Foreground sorts:
% 3.13/1.52  
% 3.13/1.52  
% 3.13/1.52  %Background operators:
% 3.13/1.52  
% 3.13/1.52  
% 3.13/1.52  %Foreground operators:
% 3.13/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.13/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.13/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.13/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.13/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.52  
% 3.24/1.53  tff(f_76, negated_conjecture, ~(![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 3.24/1.53  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.24/1.53  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.24/1.53  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.24/1.53  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.24/1.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.24/1.53  tff(c_34, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.24/1.53  tff(c_30, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.24/1.53  tff(c_45, plain, (![B_19, A_20]: (m1_subset_1(B_19, A_20) | ~v1_xboole_0(B_19) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.53  tff(c_26, plain, (~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.24/1.53  tff(c_49, plain, (~v1_xboole_0(k1_funct_1('#skF_5', '#skF_4')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_45, c_26])).
% 3.24/1.53  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_49])).
% 3.24/1.53  tff(c_32, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.24/1.53  tff(c_28, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.24/1.53  tff(c_22, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.24/1.53  tff(c_138, plain, (![B_45, A_46]: (r2_hidden(k1_funct_1(B_45, A_46), k2_relat_1(B_45)) | ~r2_hidden(A_46, k1_relat_1(B_45)) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.24/1.53  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.24/1.53  tff(c_475, plain, (![B_109, A_110, B_111]: (r2_hidden(k1_funct_1(B_109, A_110), B_111) | ~r1_tarski(k2_relat_1(B_109), B_111) | ~r2_hidden(A_110, k1_relat_1(B_109)) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_138, c_6])).
% 3.24/1.53  tff(c_12, plain, (![B_11, A_10]: (m1_subset_1(B_11, A_10) | ~r2_hidden(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.53  tff(c_587, plain, (![B_131, A_132, B_133]: (m1_subset_1(k1_funct_1(B_131, A_132), B_133) | v1_xboole_0(B_133) | ~r1_tarski(k2_relat_1(B_131), B_133) | ~r2_hidden(A_132, k1_relat_1(B_131)) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131))), inference(resolution, [status(thm)], [c_475, c_12])).
% 3.24/1.53  tff(c_657, plain, (![B_147, A_148, A_149]: (m1_subset_1(k1_funct_1(B_147, A_148), A_149) | v1_xboole_0(A_149) | ~r2_hidden(A_148, k1_relat_1(B_147)) | ~v1_funct_1(B_147) | ~v5_relat_1(B_147, A_149) | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_22, c_587])).
% 3.24/1.53  tff(c_683, plain, (![A_149]: (m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), A_149) | v1_xboole_0(A_149) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_149) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_657])).
% 3.24/1.53  tff(c_695, plain, (![A_150]: (m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), A_150) | v1_xboole_0(A_150) | ~v5_relat_1('#skF_5', A_150))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_683])).
% 3.24/1.53  tff(c_704, plain, (v1_xboole_0('#skF_3') | ~v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_695, c_26])).
% 3.24/1.53  tff(c_709, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_704])).
% 3.24/1.53  tff(c_711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_709])).
% 3.24/1.53  tff(c_713, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_49])).
% 3.24/1.53  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.53  tff(c_771, plain, (![C_167, B_168, A_169]: (r2_hidden(C_167, B_168) | ~r2_hidden(C_167, A_169) | ~r1_tarski(A_169, B_168))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.24/1.53  tff(c_813, plain, (![A_176, B_177]: (r2_hidden('#skF_1'(A_176), B_177) | ~r1_tarski(A_176, B_177) | v1_xboole_0(A_176))), inference(resolution, [status(thm)], [c_4, c_771])).
% 3.24/1.53  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.24/1.53  tff(c_825, plain, (![B_178, A_179]: (~v1_xboole_0(B_178) | ~r1_tarski(A_179, B_178) | v1_xboole_0(A_179))), inference(resolution, [status(thm)], [c_813, c_2])).
% 3.24/1.53  tff(c_867, plain, (![A_186, B_187]: (~v1_xboole_0(A_186) | v1_xboole_0(k2_relat_1(B_187)) | ~v5_relat_1(B_187, A_186) | ~v1_relat_1(B_187))), inference(resolution, [status(thm)], [c_22, c_825])).
% 3.24/1.53  tff(c_871, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0(k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_867])).
% 3.24/1.53  tff(c_875, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_713, c_871])).
% 3.24/1.53  tff(c_844, plain, (![B_182, A_183]: (r2_hidden(k1_funct_1(B_182, A_183), k2_relat_1(B_182)) | ~r2_hidden(A_183, k1_relat_1(B_182)) | ~v1_funct_1(B_182) | ~v1_relat_1(B_182))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.24/1.53  tff(c_925, plain, (![B_198, A_199]: (~v1_xboole_0(k2_relat_1(B_198)) | ~r2_hidden(A_199, k1_relat_1(B_198)) | ~v1_funct_1(B_198) | ~v1_relat_1(B_198))), inference(resolution, [status(thm)], [c_844, c_2])).
% 3.24/1.53  tff(c_948, plain, (~v1_xboole_0(k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_925])).
% 3.24/1.53  tff(c_957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_875, c_948])).
% 3.24/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.53  
% 3.24/1.53  Inference rules
% 3.24/1.53  ----------------------
% 3.24/1.53  #Ref     : 0
% 3.24/1.53  #Sup     : 204
% 3.24/1.53  #Fact    : 0
% 3.24/1.53  #Define  : 0
% 3.24/1.53  #Split   : 1
% 3.24/1.53  #Chain   : 0
% 3.24/1.53  #Close   : 0
% 3.24/1.53  
% 3.24/1.53  Ordering : KBO
% 3.24/1.53  
% 3.24/1.53  Simplification rules
% 3.24/1.53  ----------------------
% 3.24/1.53  #Subsume      : 65
% 3.24/1.53  #Demod        : 33
% 3.24/1.53  #Tautology    : 33
% 3.24/1.53  #SimpNegUnit  : 4
% 3.24/1.53  #BackRed      : 0
% 3.24/1.53  
% 3.24/1.53  #Partial instantiations: 0
% 3.24/1.53  #Strategies tried      : 1
% 3.24/1.53  
% 3.24/1.53  Timing (in seconds)
% 3.24/1.53  ----------------------
% 3.24/1.53  Preprocessing        : 0.30
% 3.24/1.53  Parsing              : 0.16
% 3.24/1.53  CNF conversion       : 0.02
% 3.24/1.53  Main loop            : 0.42
% 3.24/1.53  Inferencing          : 0.17
% 3.24/1.53  Reduction            : 0.10
% 3.24/1.53  Demodulation         : 0.06
% 3.24/1.53  BG Simplification    : 0.02
% 3.24/1.53  Subsumption          : 0.10
% 3.24/1.53  Abstraction          : 0.02
% 3.24/1.54  MUC search           : 0.00
% 3.24/1.54  Cooper               : 0.00
% 3.24/1.54  Total                : 0.75
% 3.24/1.54  Index Insertion      : 0.00
% 3.24/1.54  Index Deletion       : 0.00
% 3.24/1.54  Index Matching       : 0.00
% 3.24/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
