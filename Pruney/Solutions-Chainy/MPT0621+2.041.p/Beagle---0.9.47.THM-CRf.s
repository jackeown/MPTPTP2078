%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:04 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 106 expanded)
%              Number of leaves         :   15 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 ( 332 expanded)
%              Number of equality atoms :   44 ( 175 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_3,B_4] : v1_funct_1('#skF_2'(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_relat_1('#skF_2'(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_3,B_4] : v1_relat_1('#skF_2'(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [C_26,B_27] :
      ( C_26 = B_27
      | k1_relat_1(C_26) != '#skF_3'
      | k1_relat_1(B_27) != '#skF_3'
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    ! [B_27,A_3,B_4] :
      ( B_27 = '#skF_2'(A_3,B_4)
      | k1_relat_1('#skF_2'(A_3,B_4)) != '#skF_3'
      | k1_relat_1(B_27) != '#skF_3'
      | ~ v1_funct_1('#skF_2'(A_3,B_4))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_10,c_36])).

tff(c_43,plain,(
    ! [B_28,A_29,B_30] :
      ( B_28 = '#skF_2'(A_29,B_30)
      | A_29 != '#skF_3'
      | k1_relat_1(B_28) != '#skF_3'
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_38])).

tff(c_45,plain,(
    ! [A_3,B_4,A_29,B_30] :
      ( '#skF_2'(A_3,B_4) = '#skF_2'(A_29,B_30)
      | A_29 != '#skF_3'
      | k1_relat_1('#skF_2'(A_3,B_4)) != '#skF_3'
      | ~ v1_funct_1('#skF_2'(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_10,c_43])).

tff(c_50,plain,(
    ! [A_33,B_34,A_31,B_32] :
      ( '#skF_2'(A_33,B_34) = '#skF_2'(A_31,B_32)
      | A_33 != '#skF_3'
      | A_31 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_45])).

tff(c_4,plain,(
    ! [A_3,B_4,D_9] :
      ( k1_funct_1('#skF_2'(A_3,B_4),D_9) = B_4
      | ~ r2_hidden(D_9,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_102,plain,(
    ! [A_35,B_39,B_36,A_37,D_38] :
      ( k1_funct_1('#skF_2'(A_35,B_39),D_38) = B_36
      | ~ r2_hidden(D_38,A_37)
      | A_35 != '#skF_3'
      | A_37 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_4])).

tff(c_175,plain,(
    ! [A_42,B_43,A_44] :
      ( k1_funct_1('#skF_2'(A_42,B_43),'#skF_1'(A_44)) = k1_xboole_0
      | A_42 != '#skF_3'
      | A_44 != '#skF_3'
      | k1_xboole_0 = A_44 ) ),
    inference(resolution,[status(thm)],[c_2,c_102])).

tff(c_178,plain,(
    ! [B_43,A_44,A_42] :
      ( k1_xboole_0 = B_43
      | ~ r2_hidden('#skF_1'(A_44),A_42)
      | A_42 != '#skF_3'
      | A_44 != '#skF_3'
      | k1_xboole_0 = A_44 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_4])).

tff(c_253,plain,(
    ! [A_143,A_144] :
      ( ~ r2_hidden('#skF_1'(A_143),A_144)
      | A_144 != '#skF_3'
      | A_143 != '#skF_3'
      | k1_xboole_0 = A_143 ) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_260,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2,c_253])).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_12])).

tff(c_269,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_267,plain,(
    ! [B_43] : k1_xboole_0 = B_43 ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_292,plain,(
    ! [B_224] : B_224 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_267])).

tff(c_316,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:36:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.23  
% 2.17/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.23  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.17/1.23  
% 2.17/1.23  %Foreground sorts:
% 2.17/1.23  
% 2.17/1.23  
% 2.17/1.23  %Background operators:
% 2.17/1.23  
% 2.17/1.23  
% 2.17/1.23  %Foreground operators:
% 2.17/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.17/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.23  
% 2.17/1.24  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.17/1.24  tff(f_45, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 2.17/1.24  tff(f_64, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 2.17/1.24  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.24  tff(c_8, plain, (![A_3, B_4]: (v1_funct_1('#skF_2'(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.24  tff(c_6, plain, (![A_3, B_4]: (k1_relat_1('#skF_2'(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.24  tff(c_10, plain, (![A_3, B_4]: (v1_relat_1('#skF_2'(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.24  tff(c_36, plain, (![C_26, B_27]: (C_26=B_27 | k1_relat_1(C_26)!='#skF_3' | k1_relat_1(B_27)!='#skF_3' | ~v1_funct_1(C_26) | ~v1_relat_1(C_26) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.17/1.24  tff(c_38, plain, (![B_27, A_3, B_4]: (B_27='#skF_2'(A_3, B_4) | k1_relat_1('#skF_2'(A_3, B_4))!='#skF_3' | k1_relat_1(B_27)!='#skF_3' | ~v1_funct_1('#skF_2'(A_3, B_4)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_10, c_36])).
% 2.17/1.24  tff(c_43, plain, (![B_28, A_29, B_30]: (B_28='#skF_2'(A_29, B_30) | A_29!='#skF_3' | k1_relat_1(B_28)!='#skF_3' | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6, c_38])).
% 2.17/1.24  tff(c_45, plain, (![A_3, B_4, A_29, B_30]: ('#skF_2'(A_3, B_4)='#skF_2'(A_29, B_30) | A_29!='#skF_3' | k1_relat_1('#skF_2'(A_3, B_4))!='#skF_3' | ~v1_funct_1('#skF_2'(A_3, B_4)))), inference(resolution, [status(thm)], [c_10, c_43])).
% 2.17/1.24  tff(c_50, plain, (![A_33, B_34, A_31, B_32]: ('#skF_2'(A_33, B_34)='#skF_2'(A_31, B_32) | A_33!='#skF_3' | A_31!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6, c_45])).
% 2.17/1.24  tff(c_4, plain, (![A_3, B_4, D_9]: (k1_funct_1('#skF_2'(A_3, B_4), D_9)=B_4 | ~r2_hidden(D_9, A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.24  tff(c_102, plain, (![A_35, B_39, B_36, A_37, D_38]: (k1_funct_1('#skF_2'(A_35, B_39), D_38)=B_36 | ~r2_hidden(D_38, A_37) | A_35!='#skF_3' | A_37!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_50, c_4])).
% 2.17/1.24  tff(c_175, plain, (![A_42, B_43, A_44]: (k1_funct_1('#skF_2'(A_42, B_43), '#skF_1'(A_44))=k1_xboole_0 | A_42!='#skF_3' | A_44!='#skF_3' | k1_xboole_0=A_44)), inference(resolution, [status(thm)], [c_2, c_102])).
% 2.17/1.24  tff(c_178, plain, (![B_43, A_44, A_42]: (k1_xboole_0=B_43 | ~r2_hidden('#skF_1'(A_44), A_42) | A_42!='#skF_3' | A_44!='#skF_3' | k1_xboole_0=A_44)), inference(superposition, [status(thm), theory('equality')], [c_175, c_4])).
% 2.17/1.24  tff(c_253, plain, (![A_143, A_144]: (~r2_hidden('#skF_1'(A_143), A_144) | A_144!='#skF_3' | A_143!='#skF_3' | k1_xboole_0=A_143)), inference(splitLeft, [status(thm)], [c_178])).
% 2.17/1.24  tff(c_260, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2, c_253])).
% 2.17/1.24  tff(c_12, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.17/1.24  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_12])).
% 2.17/1.24  tff(c_269, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_178])).
% 2.17/1.24  tff(c_267, plain, (![B_43]: (k1_xboole_0=B_43)), inference(splitRight, [status(thm)], [c_178])).
% 2.17/1.24  tff(c_292, plain, (![B_224]: (B_224='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_269, c_267])).
% 2.17/1.24  tff(c_316, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_292, c_12])).
% 2.17/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  Inference rules
% 2.17/1.24  ----------------------
% 2.17/1.24  #Ref     : 1
% 2.17/1.24  #Sup     : 83
% 2.17/1.24  #Fact    : 0
% 2.17/1.24  #Define  : 0
% 2.17/1.24  #Split   : 1
% 2.17/1.24  #Chain   : 0
% 2.17/1.24  #Close   : 0
% 2.17/1.24  
% 2.17/1.24  Ordering : KBO
% 2.17/1.24  
% 2.17/1.24  Simplification rules
% 2.17/1.24  ----------------------
% 2.17/1.24  #Subsume      : 29
% 2.17/1.24  #Demod        : 14
% 2.17/1.24  #Tautology    : 11
% 2.17/1.24  #SimpNegUnit  : 0
% 2.17/1.24  #BackRed      : 2
% 2.17/1.24  
% 2.17/1.24  #Partial instantiations: 97
% 2.17/1.24  #Strategies tried      : 1
% 2.17/1.24  
% 2.17/1.24  Timing (in seconds)
% 2.17/1.24  ----------------------
% 2.17/1.25  Preprocessing        : 0.26
% 2.17/1.25  Parsing              : 0.14
% 2.17/1.25  CNF conversion       : 0.02
% 2.17/1.25  Main loop            : 0.22
% 2.17/1.25  Inferencing          : 0.09
% 2.17/1.25  Reduction            : 0.05
% 2.17/1.25  Demodulation         : 0.04
% 2.17/1.25  BG Simplification    : 0.01
% 2.17/1.25  Subsumption          : 0.05
% 2.17/1.25  Abstraction          : 0.01
% 2.17/1.25  MUC search           : 0.00
% 2.17/1.25  Cooper               : 0.00
% 2.17/1.25  Total                : 0.50
% 2.17/1.25  Index Insertion      : 0.00
% 2.17/1.25  Index Deletion       : 0.00
% 2.17/1.25  Index Matching       : 0.00
% 2.17/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
