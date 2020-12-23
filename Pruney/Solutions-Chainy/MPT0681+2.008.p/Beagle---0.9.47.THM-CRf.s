%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:26 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   45 (  53 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  93 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_47,axiom,(
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

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_235,plain,(
    ! [C_43,A_44,B_45] :
      ( k3_xboole_0(k9_relat_1(C_43,A_44),k9_relat_1(C_43,B_45)) = k9_relat_1(C_43,k3_xboole_0(A_44,B_45))
      | ~ v2_funct_1(C_43)
      | ~ v1_funct_1(C_43)
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_62,plain,(
    k3_xboole_0(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_24])).

tff(c_241,plain,
    ( k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')) != k1_xboole_0
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_62])).

tff(c_251,plain,(
    k9_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_57,c_241])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_87,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,B_29)
      | ~ r2_hidden(C_30,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_97,plain,(
    ! [C_31] : ~ r2_hidden(C_31,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_87])).

tff(c_106,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_97])).

tff(c_220,plain,(
    ! [B_41,A_42] :
      ( k9_relat_1(B_41,A_42) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_41),A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_253,plain,(
    ! [B_46] :
      ( k9_relat_1(B_46,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_106,c_220])).

tff(c_256,plain,(
    k9_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_253])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:19:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.26  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.03/1.26  
% 2.03/1.26  %Foreground sorts:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Background operators:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Foreground operators:
% 2.03/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.03/1.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.03/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.03/1.26  
% 2.03/1.27  tff(f_86, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 2.03/1.27  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.03/1.27  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 2.03/1.27  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.03/1.27  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.03/1.27  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.03/1.27  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.03/1.27  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.03/1.27  tff(c_26, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.03/1.27  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.03/1.27  tff(c_46, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.27  tff(c_57, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_46])).
% 2.03/1.27  tff(c_235, plain, (![C_43, A_44, B_45]: (k3_xboole_0(k9_relat_1(C_43, A_44), k9_relat_1(C_43, B_45))=k9_relat_1(C_43, k3_xboole_0(A_44, B_45)) | ~v2_funct_1(C_43) | ~v1_funct_1(C_43) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.03/1.27  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.27  tff(c_24, plain, (~r1_xboole_0(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.03/1.27  tff(c_62, plain, (k3_xboole_0(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_24])).
% 2.03/1.27  tff(c_241, plain, (k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0 | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_235, c_62])).
% 2.03/1.27  tff(c_251, plain, (k9_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_57, c_241])).
% 2.03/1.27  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.27  tff(c_12, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.03/1.27  tff(c_87, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, B_29) | ~r2_hidden(C_30, A_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.27  tff(c_97, plain, (![C_31]: (~r2_hidden(C_31, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_87])).
% 2.03/1.27  tff(c_106, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_97])).
% 2.03/1.27  tff(c_220, plain, (![B_41, A_42]: (k9_relat_1(B_41, A_42)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_41), A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.03/1.27  tff(c_253, plain, (![B_46]: (k9_relat_1(B_46, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_106, c_220])).
% 2.03/1.27  tff(c_256, plain, (k9_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_253])).
% 2.03/1.27  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_251, c_256])).
% 2.03/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.27  
% 2.03/1.27  Inference rules
% 2.03/1.27  ----------------------
% 2.03/1.27  #Ref     : 0
% 2.03/1.27  #Sup     : 51
% 2.03/1.27  #Fact    : 0
% 2.03/1.27  #Define  : 0
% 2.03/1.27  #Split   : 0
% 2.03/1.27  #Chain   : 0
% 2.03/1.27  #Close   : 0
% 2.03/1.27  
% 2.03/1.27  Ordering : KBO
% 2.03/1.27  
% 2.03/1.27  Simplification rules
% 2.03/1.27  ----------------------
% 2.03/1.27  #Subsume      : 3
% 2.03/1.27  #Demod        : 7
% 2.03/1.27  #Tautology    : 27
% 2.03/1.27  #SimpNegUnit  : 1
% 2.03/1.27  #BackRed      : 0
% 2.03/1.27  
% 2.03/1.27  #Partial instantiations: 0
% 2.03/1.27  #Strategies tried      : 1
% 2.03/1.27  
% 2.03/1.27  Timing (in seconds)
% 2.03/1.27  ----------------------
% 2.03/1.28  Preprocessing        : 0.29
% 2.03/1.28  Parsing              : 0.16
% 2.03/1.28  CNF conversion       : 0.02
% 2.03/1.28  Main loop            : 0.19
% 2.03/1.28  Inferencing          : 0.08
% 2.03/1.28  Reduction            : 0.05
% 2.03/1.28  Demodulation         : 0.04
% 2.03/1.28  BG Simplification    : 0.01
% 2.03/1.28  Subsumption          : 0.04
% 2.03/1.28  Abstraction          : 0.01
% 2.03/1.28  MUC search           : 0.00
% 2.03/1.28  Cooper               : 0.00
% 2.03/1.28  Total                : 0.51
% 2.03/1.28  Index Insertion      : 0.00
% 2.03/1.28  Index Deletion       : 0.00
% 2.03/1.28  Index Matching       : 0.00
% 2.03/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
