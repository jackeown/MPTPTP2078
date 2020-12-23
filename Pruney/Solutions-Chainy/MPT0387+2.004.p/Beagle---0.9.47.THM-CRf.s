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
% DateTime   : Thu Dec  3 09:57:11 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  69 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 134 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( r2_hidden(k1_xboole_0,A)
       => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_49,axiom,(
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

tff(f_80,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(c_40,plain,(
    r2_hidden(k1_xboole_0,'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    ! [B_30,A_31] :
      ( ~ r2_hidden(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_46])).

tff(c_38,plain,(
    k1_setfam_1('#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_85,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,B_44)
      | ~ r2_hidden(C_45,B_44)
      | ~ r2_hidden(C_45,A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,(
    ! [C_45] : ~ r2_hidden(C_45,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_85])).

tff(c_111,plain,(
    ! [C_47,D_48,A_49] :
      ( r2_hidden(C_47,D_48)
      | ~ r2_hidden(D_48,A_49)
      | ~ r2_hidden(C_47,k1_setfam_1(A_49))
      | k1_xboole_0 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_119,plain,(
    ! [C_47] :
      ( r2_hidden(C_47,k1_xboole_0)
      | ~ r2_hidden(C_47,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_40,c_111])).

tff(c_125,plain,(
    ! [C_47] :
      ( ~ r2_hidden(C_47,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_119])).

tff(c_153,plain,(
    ! [C_52] : ~ r2_hidden(C_52,k1_setfam_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_168,plain,(
    v1_xboole_0(k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_153])).

tff(c_62,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_2'(A_34,B_35),B_35)
      | r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [B_38,A_39] :
      ( ~ v1_xboole_0(B_38)
      | r1_xboole_0(A_39,B_38) ) ),
    inference(resolution,[status(thm)],[c_62,c_2])).

tff(c_14,plain,(
    ! [A_10] :
      ( ~ r1_xboole_0(A_10,A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,(
    ! [B_38] :
      ( k1_xboole_0 = B_38
      | ~ v1_xboole_0(B_38) ) ),
    inference(resolution,[status(thm)],[c_72,c_14])).

tff(c_171,plain,(
    k1_setfam_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_168,c_77])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_171])).

tff(c_176,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_95,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_85])).

tff(c_110,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_95])).

tff(c_179,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_110])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:49:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.21  
% 2.20/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.21  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 2.20/1.21  
% 2.20/1.21  %Foreground sorts:
% 2.20/1.21  
% 2.20/1.21  
% 2.20/1.21  %Background operators:
% 2.20/1.21  
% 2.20/1.21  
% 2.20/1.21  %Foreground operators:
% 2.20/1.21  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.20/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.20/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.21  tff('#skF_7', type, '#skF_7': $i).
% 2.20/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.20/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.20/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.21  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.20/1.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.20/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.20/1.21  
% 2.20/1.22  tff(f_85, negated_conjecture, ~(![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_setfam_1)).
% 2.20/1.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.20/1.22  tff(f_61, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.20/1.22  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.20/1.22  tff(f_80, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.20/1.22  tff(c_40, plain, (r2_hidden(k1_xboole_0, '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.20/1.22  tff(c_46, plain, (![B_30, A_31]: (~r2_hidden(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.22  tff(c_50, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_40, c_46])).
% 2.20/1.22  tff(c_38, plain, (k1_setfam_1('#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.20/1.22  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.22  tff(c_12, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.20/1.22  tff(c_85, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, B_44) | ~r2_hidden(C_45, B_44) | ~r2_hidden(C_45, A_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.20/1.22  tff(c_94, plain, (![C_45]: (~r2_hidden(C_45, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_85])).
% 2.20/1.22  tff(c_111, plain, (![C_47, D_48, A_49]: (r2_hidden(C_47, D_48) | ~r2_hidden(D_48, A_49) | ~r2_hidden(C_47, k1_setfam_1(A_49)) | k1_xboole_0=A_49)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.20/1.22  tff(c_119, plain, (![C_47]: (r2_hidden(C_47, k1_xboole_0) | ~r2_hidden(C_47, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_40, c_111])).
% 2.20/1.22  tff(c_125, plain, (![C_47]: (~r2_hidden(C_47, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_94, c_119])).
% 2.20/1.22  tff(c_153, plain, (![C_52]: (~r2_hidden(C_52, k1_setfam_1('#skF_7')))), inference(splitLeft, [status(thm)], [c_125])).
% 2.20/1.22  tff(c_168, plain, (v1_xboole_0(k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_4, c_153])).
% 2.20/1.22  tff(c_62, plain, (![A_34, B_35]: (r2_hidden('#skF_2'(A_34, B_35), B_35) | r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.20/1.22  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.22  tff(c_72, plain, (![B_38, A_39]: (~v1_xboole_0(B_38) | r1_xboole_0(A_39, B_38))), inference(resolution, [status(thm)], [c_62, c_2])).
% 2.20/1.22  tff(c_14, plain, (![A_10]: (~r1_xboole_0(A_10, A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.20/1.22  tff(c_77, plain, (![B_38]: (k1_xboole_0=B_38 | ~v1_xboole_0(B_38))), inference(resolution, [status(thm)], [c_72, c_14])).
% 2.20/1.22  tff(c_171, plain, (k1_setfam_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_168, c_77])).
% 2.20/1.22  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_171])).
% 2.20/1.22  tff(c_176, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_125])).
% 2.20/1.22  tff(c_95, plain, (![C_46]: (~r2_hidden(C_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_85])).
% 2.20/1.22  tff(c_110, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_95])).
% 2.20/1.22  tff(c_179, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_110])).
% 2.20/1.22  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_179])).
% 2.20/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.22  
% 2.20/1.22  Inference rules
% 2.20/1.22  ----------------------
% 2.20/1.22  #Ref     : 0
% 2.20/1.22  #Sup     : 28
% 2.20/1.22  #Fact    : 0
% 2.20/1.22  #Define  : 0
% 2.20/1.22  #Split   : 1
% 2.20/1.22  #Chain   : 0
% 2.20/1.22  #Close   : 0
% 2.20/1.22  
% 2.20/1.22  Ordering : KBO
% 2.20/1.22  
% 2.20/1.22  Simplification rules
% 2.20/1.22  ----------------------
% 2.20/1.22  #Subsume      : 5
% 2.20/1.22  #Demod        : 13
% 2.20/1.22  #Tautology    : 9
% 2.20/1.22  #SimpNegUnit  : 3
% 2.20/1.22  #BackRed      : 10
% 2.20/1.22  
% 2.20/1.22  #Partial instantiations: 0
% 2.20/1.22  #Strategies tried      : 1
% 2.20/1.23  
% 2.20/1.23  Timing (in seconds)
% 2.20/1.23  ----------------------
% 2.20/1.23  Preprocessing        : 0.30
% 2.20/1.23  Parsing              : 0.15
% 2.20/1.23  CNF conversion       : 0.02
% 2.20/1.23  Main loop            : 0.17
% 2.20/1.23  Inferencing          : 0.06
% 2.20/1.23  Reduction            : 0.05
% 2.20/1.23  Demodulation         : 0.03
% 2.20/1.23  BG Simplification    : 0.02
% 2.20/1.23  Subsumption          : 0.04
% 2.20/1.23  Abstraction          : 0.01
% 2.20/1.23  MUC search           : 0.00
% 2.20/1.23  Cooper               : 0.00
% 2.20/1.23  Total                : 0.49
% 2.20/1.23  Index Insertion      : 0.00
% 2.20/1.23  Index Deletion       : 0.00
% 2.20/1.23  Index Matching       : 0.00
% 2.20/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
