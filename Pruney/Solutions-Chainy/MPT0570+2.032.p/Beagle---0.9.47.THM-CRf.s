%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:45 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   49 (  77 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 164 expanded)
%              Number of equality atoms :   22 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_214,plain,(
    ! [B_56,A_57] :
      ( r1_xboole_0(k2_relat_1(B_56),A_57)
      | k10_relat_1(B_56,A_57) != k1_xboole_0
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_225,plain,(
    ! [B_56,A_57] :
      ( k4_xboole_0(k2_relat_1(B_56),A_57) = k2_relat_1(B_56)
      | k10_relat_1(B_56,A_57) != k1_xboole_0
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_214,c_20])).

tff(c_30,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_125,plain,(
    ! [C_43,B_44,A_45] :
      ( r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,(
    ! [A_6,B_7,B_44] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_44)
      | ~ r1_tarski(B_7,B_44)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_82,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,B_37)
      | ~ r2_hidden(C_38,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_226,plain,(
    ! [C_58,B_59,A_60] :
      ( ~ r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | k4_xboole_0(A_60,B_59) != A_60 ) ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_682,plain,(
    ! [A_115,B_116,A_117] :
      ( ~ r2_hidden('#skF_2'(A_115,B_116),A_117)
      | k4_xboole_0(A_117,B_116) != A_117
      | r1_xboole_0(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_10,c_226])).

tff(c_776,plain,(
    ! [B_129,B_130,A_131] :
      ( k4_xboole_0(B_129,B_130) != B_129
      | ~ r1_tarski(B_130,B_129)
      | r1_xboole_0(A_131,B_130) ) ),
    inference(resolution,[status(thm)],[c_134,c_682])).

tff(c_789,plain,(
    ! [A_131] :
      ( k4_xboole_0(k2_relat_1('#skF_4'),'#skF_3') != k2_relat_1('#skF_4')
      | r1_xboole_0(A_131,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_776])).

tff(c_790,plain,(
    k4_xboole_0(k2_relat_1('#skF_4'),'#skF_3') != k2_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_789])).

tff(c_809,plain,
    ( k10_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_790])).

tff(c_817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_809])).

tff(c_820,plain,(
    ! [A_135] : r1_xboole_0(A_135,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_789])).

tff(c_833,plain,(
    ! [A_136] : k4_xboole_0(A_136,'#skF_3') = A_136 ),
    inference(resolution,[status(thm)],[c_820,c_20])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_34,B_35] :
      ( ~ r2_hidden('#skF_1'(A_34,B_35),B_35)
      | r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [A_39] : r1_tarski(A_39,A_39) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_93,plain,(
    ! [A_39] : k4_xboole_0(A_39,A_39) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_89,c_16])).

tff(c_857,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_833,c_93])).

tff(c_886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_857])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:08:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.40  
% 2.86/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.86/1.40  
% 2.86/1.40  %Foreground sorts:
% 2.86/1.40  
% 2.86/1.40  
% 2.86/1.40  %Background operators:
% 2.86/1.40  
% 2.86/1.40  
% 2.86/1.40  %Foreground operators:
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.86/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.86/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.86/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.86/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.86/1.40  
% 2.86/1.41  tff(f_77, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 2.86/1.41  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 2.86/1.41  tff(f_60, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.86/1.41  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.86/1.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.86/1.41  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.86/1.41  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.86/1.41  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.86/1.41  tff(c_28, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.86/1.41  tff(c_214, plain, (![B_56, A_57]: (r1_xboole_0(k2_relat_1(B_56), A_57) | k10_relat_1(B_56, A_57)!=k1_xboole_0 | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.86/1.41  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.86/1.41  tff(c_225, plain, (![B_56, A_57]: (k4_xboole_0(k2_relat_1(B_56), A_57)=k2_relat_1(B_56) | k10_relat_1(B_56, A_57)!=k1_xboole_0 | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_214, c_20])).
% 2.86/1.41  tff(c_30, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.86/1.41  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.41  tff(c_125, plain, (![C_43, B_44, A_45]: (r2_hidden(C_43, B_44) | ~r2_hidden(C_43, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.41  tff(c_134, plain, (![A_6, B_7, B_44]: (r2_hidden('#skF_2'(A_6, B_7), B_44) | ~r1_tarski(B_7, B_44) | r1_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_125])).
% 2.86/1.41  tff(c_22, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.86/1.41  tff(c_82, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, B_37) | ~r2_hidden(C_38, A_36))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.41  tff(c_226, plain, (![C_58, B_59, A_60]: (~r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | k4_xboole_0(A_60, B_59)!=A_60)), inference(resolution, [status(thm)], [c_22, c_82])).
% 2.86/1.41  tff(c_682, plain, (![A_115, B_116, A_117]: (~r2_hidden('#skF_2'(A_115, B_116), A_117) | k4_xboole_0(A_117, B_116)!=A_117 | r1_xboole_0(A_115, B_116))), inference(resolution, [status(thm)], [c_10, c_226])).
% 2.86/1.41  tff(c_776, plain, (![B_129, B_130, A_131]: (k4_xboole_0(B_129, B_130)!=B_129 | ~r1_tarski(B_130, B_129) | r1_xboole_0(A_131, B_130))), inference(resolution, [status(thm)], [c_134, c_682])).
% 2.86/1.41  tff(c_789, plain, (![A_131]: (k4_xboole_0(k2_relat_1('#skF_4'), '#skF_3')!=k2_relat_1('#skF_4') | r1_xboole_0(A_131, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_776])).
% 2.86/1.41  tff(c_790, plain, (k4_xboole_0(k2_relat_1('#skF_4'), '#skF_3')!=k2_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_789])).
% 2.86/1.41  tff(c_809, plain, (k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_225, c_790])).
% 2.86/1.41  tff(c_817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_809])).
% 2.86/1.41  tff(c_820, plain, (![A_135]: (r1_xboole_0(A_135, '#skF_3'))), inference(splitRight, [status(thm)], [c_789])).
% 2.86/1.41  tff(c_833, plain, (![A_136]: (k4_xboole_0(A_136, '#skF_3')=A_136)), inference(resolution, [status(thm)], [c_820, c_20])).
% 2.86/1.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.41  tff(c_76, plain, (![A_34, B_35]: (~r2_hidden('#skF_1'(A_34, B_35), B_35) | r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.41  tff(c_89, plain, (![A_39]: (r1_tarski(A_39, A_39))), inference(resolution, [status(thm)], [c_6, c_76])).
% 2.86/1.41  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.86/1.41  tff(c_93, plain, (![A_39]: (k4_xboole_0(A_39, A_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_89, c_16])).
% 2.86/1.41  tff(c_857, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_833, c_93])).
% 2.86/1.41  tff(c_886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_857])).
% 2.86/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.41  
% 2.86/1.41  Inference rules
% 2.86/1.41  ----------------------
% 2.86/1.41  #Ref     : 0
% 2.86/1.41  #Sup     : 201
% 2.86/1.41  #Fact    : 0
% 2.86/1.41  #Define  : 0
% 2.86/1.41  #Split   : 2
% 2.86/1.41  #Chain   : 0
% 2.86/1.41  #Close   : 0
% 2.86/1.41  
% 2.86/1.41  Ordering : KBO
% 2.86/1.41  
% 2.86/1.41  Simplification rules
% 2.86/1.41  ----------------------
% 2.86/1.41  #Subsume      : 45
% 2.86/1.41  #Demod        : 27
% 2.86/1.41  #Tautology    : 77
% 2.86/1.41  #SimpNegUnit  : 6
% 2.86/1.41  #BackRed      : 0
% 2.86/1.41  
% 2.86/1.41  #Partial instantiations: 0
% 2.86/1.41  #Strategies tried      : 1
% 2.86/1.41  
% 2.86/1.41  Timing (in seconds)
% 2.86/1.41  ----------------------
% 2.86/1.41  Preprocessing        : 0.29
% 2.86/1.41  Parsing              : 0.16
% 2.86/1.41  CNF conversion       : 0.02
% 2.86/1.41  Main loop            : 0.36
% 2.86/1.41  Inferencing          : 0.15
% 2.86/1.41  Reduction            : 0.09
% 2.86/1.41  Demodulation         : 0.06
% 2.86/1.41  BG Simplification    : 0.02
% 2.86/1.41  Subsumption          : 0.08
% 2.86/1.41  Abstraction          : 0.02
% 2.86/1.41  MUC search           : 0.00
% 2.86/1.41  Cooper               : 0.00
% 2.86/1.41  Total                : 0.68
% 2.86/1.42  Index Insertion      : 0.00
% 2.86/1.42  Index Deletion       : 0.00
% 2.86/1.42  Index Matching       : 0.00
% 2.86/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
