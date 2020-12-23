%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:32 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  41 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [A_47,B_48,C_49] :
      ( r2_hidden('#skF_3'(A_47,B_48,C_49),B_48)
      | ~ r2_hidden(C_49,A_47)
      | ~ r1_setfam_1(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_51,plain,(
    ! [A_25,B_26] : ~ r2_hidden(A_25,k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_51])).

tff(c_121,plain,(
    ! [C_50,A_51] :
      ( ~ r2_hidden(C_50,A_51)
      | ~ r1_setfam_1(A_51,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_111,c_54])).

tff(c_134,plain,(
    ! [A_52] :
      ( ~ r1_setfam_1(A_52,k1_xboole_0)
      | v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_4,c_121])).

tff(c_149,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_134])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [B_31,A_32] :
      ( ~ v1_xboole_0(B_31)
      | B_31 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_152,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_149,c_74])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:11:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  %$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 1.67/1.12  
% 1.67/1.12  %Foreground sorts:
% 1.67/1.12  
% 1.67/1.12  
% 1.67/1.12  %Background operators:
% 1.67/1.12  
% 1.67/1.12  
% 1.67/1.12  %Foreground operators:
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.12  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.67/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.67/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.67/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.67/1.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.67/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.12  
% 1.67/1.13  tff(f_66, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.67/1.13  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.67/1.13  tff(f_61, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.67/1.13  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.67/1.13  tff(f_49, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.67/1.13  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.67/1.13  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.67/1.13  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.67/1.13  tff(c_28, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.67/1.13  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.13  tff(c_111, plain, (![A_47, B_48, C_49]: (r2_hidden('#skF_3'(A_47, B_48, C_49), B_48) | ~r2_hidden(C_49, A_47) | ~r1_setfam_1(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.67/1.13  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.67/1.13  tff(c_51, plain, (![A_25, B_26]: (~r2_hidden(A_25, k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.67/1.13  tff(c_54, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_51])).
% 1.67/1.13  tff(c_121, plain, (![C_50, A_51]: (~r2_hidden(C_50, A_51) | ~r1_setfam_1(A_51, k1_xboole_0))), inference(resolution, [status(thm)], [c_111, c_54])).
% 1.67/1.13  tff(c_134, plain, (![A_52]: (~r1_setfam_1(A_52, k1_xboole_0) | v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_4, c_121])).
% 1.67/1.13  tff(c_149, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_134])).
% 1.67/1.13  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.67/1.13  tff(c_71, plain, (![B_31, A_32]: (~v1_xboole_0(B_31) | B_31=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.13  tff(c_74, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_6, c_71])).
% 1.67/1.13  tff(c_152, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_149, c_74])).
% 1.67/1.13  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_152])).
% 1.67/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  Inference rules
% 1.67/1.13  ----------------------
% 1.67/1.13  #Ref     : 0
% 1.67/1.13  #Sup     : 27
% 1.67/1.13  #Fact    : 0
% 1.67/1.13  #Define  : 0
% 1.67/1.13  #Split   : 0
% 1.67/1.13  #Chain   : 0
% 1.67/1.13  #Close   : 0
% 1.67/1.13  
% 1.67/1.13  Ordering : KBO
% 1.67/1.13  
% 1.67/1.13  Simplification rules
% 1.67/1.13  ----------------------
% 1.67/1.13  #Subsume      : 1
% 1.67/1.13  #Demod        : 2
% 1.67/1.13  #Tautology    : 13
% 1.67/1.13  #SimpNegUnit  : 1
% 1.67/1.13  #BackRed      : 0
% 1.67/1.13  
% 1.67/1.13  #Partial instantiations: 0
% 1.67/1.13  #Strategies tried      : 1
% 1.67/1.13  
% 1.67/1.13  Timing (in seconds)
% 1.67/1.13  ----------------------
% 1.67/1.14  Preprocessing        : 0.27
% 1.67/1.14  Parsing              : 0.14
% 1.67/1.14  CNF conversion       : 0.02
% 1.67/1.14  Main loop            : 0.12
% 1.67/1.14  Inferencing          : 0.05
% 1.67/1.14  Reduction            : 0.03
% 1.67/1.14  Demodulation         : 0.02
% 1.67/1.14  BG Simplification    : 0.01
% 1.67/1.14  Subsumption          : 0.02
% 1.67/1.14  Abstraction          : 0.00
% 1.67/1.14  MUC search           : 0.00
% 1.67/1.14  Cooper               : 0.00
% 1.67/1.14  Total                : 0.41
% 1.67/1.14  Index Insertion      : 0.00
% 1.67/1.14  Index Deletion       : 0.00
% 1.67/1.14  Index Matching       : 0.00
% 1.67/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
