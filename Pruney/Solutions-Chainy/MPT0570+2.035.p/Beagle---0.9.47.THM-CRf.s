%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:46 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   52 (  78 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 156 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_144,plain,(
    ! [B_44,A_45] :
      ( r1_xboole_0(k2_relat_1(B_44),A_45)
      | k10_relat_1(B_44,A_45) != k1_xboole_0
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_151,plain,(
    ! [B_44,A_45] :
      ( k4_xboole_0(k2_relat_1(B_44),A_45) = k2_relat_1(B_44)
      | k10_relat_1(B_44,A_45) != k1_xboole_0
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_144,c_20])).

tff(c_30,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_130,plain,(
    ! [C_38,B_39,A_40] :
      ( r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_137,plain,(
    ! [A_6,B_7,B_39] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_39)
      | ~ r1_tarski(A_6,B_39)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_130])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_140,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,B_42)
      | ~ r2_hidden(C_43,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_182,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | k4_xboole_0(A_52,B_51) != A_52 ) ),
    inference(resolution,[status(thm)],[c_22,c_140])).

tff(c_843,plain,(
    ! [A_111,B_112,A_113] :
      ( ~ r2_hidden('#skF_2'(A_111,B_112),A_113)
      | k4_xboole_0(A_113,A_111) != A_113
      | r1_xboole_0(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_12,c_182])).

tff(c_1157,plain,(
    ! [B_135,A_136,B_137] :
      ( k4_xboole_0(B_135,A_136) != B_135
      | ~ r1_tarski(A_136,B_135)
      | r1_xboole_0(A_136,B_137) ) ),
    inference(resolution,[status(thm)],[c_137,c_843])).

tff(c_1167,plain,(
    ! [B_137] :
      ( k4_xboole_0(k2_relat_1('#skF_4'),'#skF_3') != k2_relat_1('#skF_4')
      | r1_xboole_0('#skF_3',B_137) ) ),
    inference(resolution,[status(thm)],[c_30,c_1157])).

tff(c_1168,plain,(
    k4_xboole_0(k2_relat_1('#skF_4'),'#skF_3') != k2_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1167])).

tff(c_1177,plain,
    ( k10_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_1168])).

tff(c_1183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_1177])).

tff(c_1210,plain,(
    ! [B_140] : r1_xboole_0('#skF_3',B_140) ),
    inference(splitRight,[status(thm)],[c_1167])).

tff(c_1218,plain,(
    ! [B_141] : k4_xboole_0('#skF_3',B_141) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1210,c_20])).

tff(c_14,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_61])).

tff(c_79,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_76])).

tff(c_1251,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1218,c_79])).

tff(c_1292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1251])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.48  
% 3.13/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.13/1.48  
% 3.13/1.48  %Foreground sorts:
% 3.13/1.48  
% 3.13/1.48  
% 3.13/1.48  %Background operators:
% 3.13/1.48  
% 3.13/1.48  
% 3.13/1.48  %Foreground operators:
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.13/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.13/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.13/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.13/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.48  
% 3.13/1.49  tff(f_77, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 3.13/1.49  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 3.13/1.49  tff(f_60, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.13/1.49  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.13/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.13/1.49  tff(f_52, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.13/1.49  tff(f_54, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.13/1.49  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.13/1.49  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.13/1.49  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.13/1.49  tff(c_28, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.13/1.49  tff(c_144, plain, (![B_44, A_45]: (r1_xboole_0(k2_relat_1(B_44), A_45) | k10_relat_1(B_44, A_45)!=k1_xboole_0 | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.13/1.49  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.13/1.49  tff(c_151, plain, (![B_44, A_45]: (k4_xboole_0(k2_relat_1(B_44), A_45)=k2_relat_1(B_44) | k10_relat_1(B_44, A_45)!=k1_xboole_0 | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_144, c_20])).
% 3.13/1.49  tff(c_30, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.13/1.49  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.49  tff(c_130, plain, (![C_38, B_39, A_40]: (r2_hidden(C_38, B_39) | ~r2_hidden(C_38, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.13/1.49  tff(c_137, plain, (![A_6, B_7, B_39]: (r2_hidden('#skF_2'(A_6, B_7), B_39) | ~r1_tarski(A_6, B_39) | r1_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_12, c_130])).
% 3.13/1.49  tff(c_22, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k4_xboole_0(A_15, B_16)!=A_15)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.13/1.49  tff(c_140, plain, (![A_41, B_42, C_43]: (~r1_xboole_0(A_41, B_42) | ~r2_hidden(C_43, B_42) | ~r2_hidden(C_43, A_41))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.49  tff(c_182, plain, (![C_50, B_51, A_52]: (~r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | k4_xboole_0(A_52, B_51)!=A_52)), inference(resolution, [status(thm)], [c_22, c_140])).
% 3.13/1.49  tff(c_843, plain, (![A_111, B_112, A_113]: (~r2_hidden('#skF_2'(A_111, B_112), A_113) | k4_xboole_0(A_113, A_111)!=A_113 | r1_xboole_0(A_111, B_112))), inference(resolution, [status(thm)], [c_12, c_182])).
% 3.13/1.49  tff(c_1157, plain, (![B_135, A_136, B_137]: (k4_xboole_0(B_135, A_136)!=B_135 | ~r1_tarski(A_136, B_135) | r1_xboole_0(A_136, B_137))), inference(resolution, [status(thm)], [c_137, c_843])).
% 3.13/1.49  tff(c_1167, plain, (![B_137]: (k4_xboole_0(k2_relat_1('#skF_4'), '#skF_3')!=k2_relat_1('#skF_4') | r1_xboole_0('#skF_3', B_137))), inference(resolution, [status(thm)], [c_30, c_1157])).
% 3.13/1.49  tff(c_1168, plain, (k4_xboole_0(k2_relat_1('#skF_4'), '#skF_3')!=k2_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1167])).
% 3.13/1.49  tff(c_1177, plain, (k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_151, c_1168])).
% 3.13/1.49  tff(c_1183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_1177])).
% 3.13/1.49  tff(c_1210, plain, (![B_140]: (r1_xboole_0('#skF_3', B_140))), inference(splitRight, [status(thm)], [c_1167])).
% 3.13/1.49  tff(c_1218, plain, (![B_141]: (k4_xboole_0('#skF_3', B_141)='#skF_3')), inference(resolution, [status(thm)], [c_1210, c_20])).
% 3.13/1.49  tff(c_14, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.13/1.49  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.13/1.49  tff(c_61, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.13/1.49  tff(c_76, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_61])).
% 3.13/1.49  tff(c_79, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_76])).
% 3.13/1.49  tff(c_1251, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1218, c_79])).
% 3.13/1.49  tff(c_1292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1251])).
% 3.13/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.49  
% 3.13/1.49  Inference rules
% 3.13/1.49  ----------------------
% 3.13/1.49  #Ref     : 0
% 3.13/1.49  #Sup     : 315
% 3.13/1.49  #Fact    : 0
% 3.13/1.49  #Define  : 0
% 3.13/1.49  #Split   : 2
% 3.13/1.49  #Chain   : 0
% 3.13/1.49  #Close   : 0
% 3.13/1.49  
% 3.13/1.49  Ordering : KBO
% 3.13/1.49  
% 3.13/1.49  Simplification rules
% 3.13/1.49  ----------------------
% 3.13/1.49  #Subsume      : 43
% 3.13/1.49  #Demod        : 67
% 3.13/1.49  #Tautology    : 140
% 3.13/1.49  #SimpNegUnit  : 2
% 3.13/1.49  #BackRed      : 0
% 3.13/1.49  
% 3.13/1.49  #Partial instantiations: 0
% 3.13/1.49  #Strategies tried      : 1
% 3.13/1.50  
% 3.13/1.50  Timing (in seconds)
% 3.13/1.50  ----------------------
% 3.13/1.50  Preprocessing        : 0.30
% 3.13/1.50  Parsing              : 0.16
% 3.13/1.50  CNF conversion       : 0.02
% 3.13/1.50  Main loop            : 0.43
% 3.13/1.50  Inferencing          : 0.17
% 3.13/1.50  Reduction            : 0.12
% 3.13/1.50  Demodulation         : 0.08
% 3.13/1.50  BG Simplification    : 0.02
% 3.13/1.50  Subsumption          : 0.09
% 3.13/1.50  Abstraction          : 0.02
% 3.13/1.50  MUC search           : 0.00
% 3.13/1.50  Cooper               : 0.00
% 3.13/1.50  Total                : 0.76
% 3.13/1.50  Index Insertion      : 0.00
% 3.13/1.50  Index Deletion       : 0.00
% 3.13/1.50  Index Matching       : 0.00
% 3.13/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
