%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:23 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   41 (  57 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 113 expanded)
%              Number of equality atoms :   31 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_53,plain,(
    ! [B_24,A_25] :
      ( k11_relat_1(B_24,A_25) != k1_xboole_0
      | ~ r2_hidden(A_25,k1_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_64,plain,(
    k11_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_60])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),A_4)
      | k1_xboole_0 = A_4
      | k1_tarski(B_5) = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden(k4_tarski(A_7,B_8),C_9)
      | ~ r2_hidden(B_8,k11_relat_1(C_9,A_7))
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_691,plain,(
    ! [A_109,B_110,C_111] :
      ( k1_funct_1(A_109,B_110) = C_111
      | ~ r2_hidden(k4_tarski(B_110,C_111),A_109)
      | ~ r2_hidden(B_110,k1_relat_1(A_109))
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_746,plain,(
    ! [C_119,A_120,B_121] :
      ( k1_funct_1(C_119,A_120) = B_121
      | ~ r2_hidden(A_120,k1_relat_1(C_119))
      | ~ v1_funct_1(C_119)
      | ~ r2_hidden(B_121,k11_relat_1(C_119,A_120))
      | ~ v1_relat_1(C_119) ) ),
    inference(resolution,[status(thm)],[c_10,c_691])).

tff(c_761,plain,(
    ! [B_121] :
      ( k1_funct_1('#skF_3','#skF_2') = B_121
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_121,k11_relat_1('#skF_3','#skF_2'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_746])).

tff(c_770,plain,(
    ! [B_122] :
      ( k1_funct_1('#skF_3','#skF_2') = B_122
      | ~ r2_hidden(B_122,k11_relat_1('#skF_3','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_761])).

tff(c_786,plain,(
    ! [B_5] :
      ( '#skF_1'(k11_relat_1('#skF_3','#skF_2'),B_5) = k1_funct_1('#skF_3','#skF_2')
      | k11_relat_1('#skF_3','#skF_2') = k1_xboole_0
      | k1_tarski(B_5) = k11_relat_1('#skF_3','#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_770])).

tff(c_796,plain,(
    ! [B_123] :
      ( '#skF_1'(k11_relat_1('#skF_3','#skF_2'),B_123) = k1_funct_1('#skF_3','#skF_2')
      | k1_tarski(B_123) = k11_relat_1('#skF_3','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_786])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( '#skF_1'(A_4,B_5) != B_5
      | k1_xboole_0 = A_4
      | k1_tarski(B_5) = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_804,plain,(
    ! [B_123] :
      ( k1_funct_1('#skF_3','#skF_2') != B_123
      | k11_relat_1('#skF_3','#skF_2') = k1_xboole_0
      | k1_tarski(B_123) = k11_relat_1('#skF_3','#skF_2')
      | k1_tarski(B_123) = k11_relat_1('#skF_3','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_6])).

tff(c_827,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k11_relat_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_804])).

tff(c_26,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k11_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:44:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.50  
% 2.95/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.51  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.95/1.51  
% 2.95/1.51  %Foreground sorts:
% 2.95/1.51  
% 2.95/1.51  
% 2.95/1.51  %Background operators:
% 2.95/1.51  
% 2.95/1.51  
% 2.95/1.51  %Foreground operators:
% 2.95/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.95/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.95/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.95/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.95/1.51  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.95/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.95/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.95/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.95/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.95/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.95/1.51  
% 2.95/1.51  tff(f_83, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 2.95/1.51  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.95/1.51  tff(f_43, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 2.95/1.51  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.95/1.51  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.95/1.51  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.95/1.51  tff(c_28, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.95/1.51  tff(c_53, plain, (![B_24, A_25]: (k11_relat_1(B_24, A_25)!=k1_xboole_0 | ~r2_hidden(A_25, k1_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.95/1.51  tff(c_60, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_53])).
% 2.95/1.51  tff(c_64, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_60])).
% 2.95/1.51  tff(c_8, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), A_4) | k1_xboole_0=A_4 | k1_tarski(B_5)=A_4)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.95/1.51  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.95/1.51  tff(c_10, plain, (![A_7, B_8, C_9]: (r2_hidden(k4_tarski(A_7, B_8), C_9) | ~r2_hidden(B_8, k11_relat_1(C_9, A_7)) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.95/1.51  tff(c_691, plain, (![A_109, B_110, C_111]: (k1_funct_1(A_109, B_110)=C_111 | ~r2_hidden(k4_tarski(B_110, C_111), A_109) | ~r2_hidden(B_110, k1_relat_1(A_109)) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.95/1.51  tff(c_746, plain, (![C_119, A_120, B_121]: (k1_funct_1(C_119, A_120)=B_121 | ~r2_hidden(A_120, k1_relat_1(C_119)) | ~v1_funct_1(C_119) | ~r2_hidden(B_121, k11_relat_1(C_119, A_120)) | ~v1_relat_1(C_119))), inference(resolution, [status(thm)], [c_10, c_691])).
% 2.95/1.51  tff(c_761, plain, (![B_121]: (k1_funct_1('#skF_3', '#skF_2')=B_121 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_121, k11_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_746])).
% 2.95/1.51  tff(c_770, plain, (![B_122]: (k1_funct_1('#skF_3', '#skF_2')=B_122 | ~r2_hidden(B_122, k11_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_761])).
% 2.95/1.51  tff(c_786, plain, (![B_5]: ('#skF_1'(k11_relat_1('#skF_3', '#skF_2'), B_5)=k1_funct_1('#skF_3', '#skF_2') | k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | k1_tarski(B_5)=k11_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_770])).
% 2.95/1.51  tff(c_796, plain, (![B_123]: ('#skF_1'(k11_relat_1('#skF_3', '#skF_2'), B_123)=k1_funct_1('#skF_3', '#skF_2') | k1_tarski(B_123)=k11_relat_1('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_786])).
% 2.95/1.51  tff(c_6, plain, (![A_4, B_5]: ('#skF_1'(A_4, B_5)!=B_5 | k1_xboole_0=A_4 | k1_tarski(B_5)=A_4)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.95/1.51  tff(c_804, plain, (![B_123]: (k1_funct_1('#skF_3', '#skF_2')!=B_123 | k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | k1_tarski(B_123)=k11_relat_1('#skF_3', '#skF_2') | k1_tarski(B_123)=k11_relat_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_796, c_6])).
% 2.95/1.51  tff(c_827, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k11_relat_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_804])).
% 2.95/1.51  tff(c_26, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k11_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.95/1.51  tff(c_830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_827, c_26])).
% 2.95/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.51  
% 2.95/1.51  Inference rules
% 2.95/1.51  ----------------------
% 2.95/1.51  #Ref     : 1
% 2.95/1.51  #Sup     : 158
% 2.95/1.51  #Fact    : 2
% 2.95/1.51  #Define  : 0
% 2.95/1.51  #Split   : 4
% 2.95/1.51  #Chain   : 0
% 2.95/1.51  #Close   : 0
% 2.95/1.51  
% 2.95/1.51  Ordering : KBO
% 2.95/1.51  
% 2.95/1.51  Simplification rules
% 2.95/1.51  ----------------------
% 2.95/1.51  #Subsume      : 35
% 2.95/1.51  #Demod        : 76
% 2.95/1.51  #Tautology    : 31
% 2.95/1.51  #SimpNegUnit  : 4
% 2.95/1.51  #BackRed      : 4
% 2.95/1.52  
% 2.95/1.52  #Partial instantiations: 0
% 2.95/1.52  #Strategies tried      : 1
% 2.95/1.52  
% 2.95/1.52  Timing (in seconds)
% 2.95/1.52  ----------------------
% 2.95/1.52  Preprocessing        : 0.32
% 2.95/1.52  Parsing              : 0.17
% 2.95/1.52  CNF conversion       : 0.02
% 2.95/1.52  Main loop            : 0.40
% 2.95/1.52  Inferencing          : 0.15
% 2.95/1.52  Reduction            : 0.10
% 2.95/1.52  Demodulation         : 0.07
% 2.95/1.52  BG Simplification    : 0.02
% 2.95/1.52  Subsumption          : 0.09
% 2.95/1.52  Abstraction          : 0.03
% 2.95/1.52  MUC search           : 0.00
% 2.95/1.52  Cooper               : 0.00
% 2.95/1.52  Total                : 0.74
% 2.95/1.52  Index Insertion      : 0.00
% 2.95/1.52  Index Deletion       : 0.00
% 2.95/1.52  Index Matching       : 0.00
% 2.95/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
