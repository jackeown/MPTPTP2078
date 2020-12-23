%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:23 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   39 (  45 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 (  94 expanded)
%              Number of equality atoms :   33 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_29,plain,(
    ! [B_16,A_17] :
      ( k11_relat_1(B_16,A_17) != k1_xboole_0
      | ~ r2_hidden(A_17,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_35,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_29])).

tff(c_39,plain,(
    k11_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_35])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | k1_xboole_0 = A_1
      | k1_tarski(B_2) = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] :
      ( r2_hidden(k4_tarski(A_4,B_5),C_6)
      | ~ r2_hidden(B_5,k11_relat_1(C_6,A_4))
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_62,plain,(
    ! [C_26,A_27,B_28] :
      ( k1_funct_1(C_26,A_27) = B_28
      | ~ r2_hidden(k4_tarski(A_27,B_28),C_26)
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_82,plain,(
    ! [C_32,A_33,B_34] :
      ( k1_funct_1(C_32,A_33) = B_34
      | ~ v1_funct_1(C_32)
      | ~ r2_hidden(B_34,k11_relat_1(C_32,A_33))
      | ~ v1_relat_1(C_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_300,plain,(
    ! [C_69,A_70,B_71] :
      ( '#skF_1'(k11_relat_1(C_69,A_70),B_71) = k1_funct_1(C_69,A_70)
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69)
      | k11_relat_1(C_69,A_70) = k1_xboole_0
      | k1_tarski(B_71) = k11_relat_1(C_69,A_70) ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) != B_2
      | k1_xboole_0 = A_1
      | k1_tarski(B_2) = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_308,plain,(
    ! [C_69,A_70,B_71] :
      ( k1_funct_1(C_69,A_70) != B_71
      | k11_relat_1(C_69,A_70) = k1_xboole_0
      | k1_tarski(B_71) = k11_relat_1(C_69,A_70)
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69)
      | k11_relat_1(C_69,A_70) = k1_xboole_0
      | k1_tarski(B_71) = k11_relat_1(C_69,A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_2])).

tff(c_700,plain,(
    ! [C_69,A_70] :
      ( k11_relat_1(C_69,A_70) = k1_xboole_0
      | k1_tarski(k1_funct_1(C_69,A_70)) = k11_relat_1(C_69,A_70)
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69)
      | k11_relat_1(C_69,A_70) = k1_xboole_0
      | k1_tarski(k1_funct_1(C_69,A_70)) = k11_relat_1(C_69,A_70) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_308])).

tff(c_893,plain,(
    ! [C_115,A_116] :
      ( ~ v1_funct_1(C_115)
      | ~ v1_relat_1(C_115)
      | k11_relat_1(C_115,A_116) = k1_xboole_0
      | k1_tarski(k1_funct_1(C_115,A_116)) = k11_relat_1(C_115,A_116) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_700])).

tff(c_20,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k11_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_903,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k11_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_20])).

tff(c_912,plain,(
    k11_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_903])).

tff(c_914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_912])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.52  
% 3.19/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.52  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.19/1.52  
% 3.19/1.52  %Foreground sorts:
% 3.19/1.52  
% 3.19/1.52  
% 3.19/1.52  %Background operators:
% 3.19/1.52  
% 3.19/1.52  
% 3.19/1.52  %Foreground operators:
% 3.19/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.19/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.19/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.52  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.19/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.19/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.19/1.52  
% 3.45/1.53  tff(f_71, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.45/1.53  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.45/1.53  tff(f_39, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 3.45/1.53  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.45/1.53  tff(f_62, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.45/1.53  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.45/1.53  tff(c_22, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.45/1.53  tff(c_29, plain, (![B_16, A_17]: (k11_relat_1(B_16, A_17)!=k1_xboole_0 | ~r2_hidden(A_17, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.45/1.53  tff(c_35, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_29])).
% 3.45/1.53  tff(c_39, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_35])).
% 3.45/1.53  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.45/1.53  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | k1_xboole_0=A_1 | k1_tarski(B_2)=A_1)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.45/1.53  tff(c_6, plain, (![A_4, B_5, C_6]: (r2_hidden(k4_tarski(A_4, B_5), C_6) | ~r2_hidden(B_5, k11_relat_1(C_6, A_4)) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.45/1.53  tff(c_62, plain, (![C_26, A_27, B_28]: (k1_funct_1(C_26, A_27)=B_28 | ~r2_hidden(k4_tarski(A_27, B_28), C_26) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.45/1.53  tff(c_82, plain, (![C_32, A_33, B_34]: (k1_funct_1(C_32, A_33)=B_34 | ~v1_funct_1(C_32) | ~r2_hidden(B_34, k11_relat_1(C_32, A_33)) | ~v1_relat_1(C_32))), inference(resolution, [status(thm)], [c_6, c_62])).
% 3.45/1.53  tff(c_300, plain, (![C_69, A_70, B_71]: ('#skF_1'(k11_relat_1(C_69, A_70), B_71)=k1_funct_1(C_69, A_70) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69) | k11_relat_1(C_69, A_70)=k1_xboole_0 | k1_tarski(B_71)=k11_relat_1(C_69, A_70))), inference(resolution, [status(thm)], [c_4, c_82])).
% 3.45/1.53  tff(c_2, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)!=B_2 | k1_xboole_0=A_1 | k1_tarski(B_2)=A_1)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.45/1.53  tff(c_308, plain, (![C_69, A_70, B_71]: (k1_funct_1(C_69, A_70)!=B_71 | k11_relat_1(C_69, A_70)=k1_xboole_0 | k1_tarski(B_71)=k11_relat_1(C_69, A_70) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69) | k11_relat_1(C_69, A_70)=k1_xboole_0 | k1_tarski(B_71)=k11_relat_1(C_69, A_70))), inference(superposition, [status(thm), theory('equality')], [c_300, c_2])).
% 3.45/1.53  tff(c_700, plain, (![C_69, A_70]: (k11_relat_1(C_69, A_70)=k1_xboole_0 | k1_tarski(k1_funct_1(C_69, A_70))=k11_relat_1(C_69, A_70) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69) | k11_relat_1(C_69, A_70)=k1_xboole_0 | k1_tarski(k1_funct_1(C_69, A_70))=k11_relat_1(C_69, A_70))), inference(reflexivity, [status(thm), theory('equality')], [c_308])).
% 3.45/1.53  tff(c_893, plain, (![C_115, A_116]: (~v1_funct_1(C_115) | ~v1_relat_1(C_115) | k11_relat_1(C_115, A_116)=k1_xboole_0 | k1_tarski(k1_funct_1(C_115, A_116))=k11_relat_1(C_115, A_116))), inference(factorization, [status(thm), theory('equality')], [c_700])).
% 3.45/1.53  tff(c_20, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k11_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.45/1.53  tff(c_903, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_893, c_20])).
% 3.45/1.53  tff(c_912, plain, (k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_903])).
% 3.45/1.53  tff(c_914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_912])).
% 3.45/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.53  
% 3.45/1.53  Inference rules
% 3.45/1.53  ----------------------
% 3.45/1.53  #Ref     : 1
% 3.45/1.53  #Sup     : 205
% 3.45/1.53  #Fact    : 3
% 3.45/1.53  #Define  : 0
% 3.45/1.53  #Split   : 3
% 3.45/1.53  #Chain   : 0
% 3.45/1.53  #Close   : 0
% 3.45/1.53  
% 3.45/1.53  Ordering : KBO
% 3.45/1.53  
% 3.45/1.53  Simplification rules
% 3.45/1.53  ----------------------
% 3.45/1.53  #Subsume      : 50
% 3.45/1.53  #Demod        : 3
% 3.45/1.53  #Tautology    : 28
% 3.45/1.53  #SimpNegUnit  : 11
% 3.45/1.53  #BackRed      : 0
% 3.45/1.53  
% 3.45/1.53  #Partial instantiations: 0
% 3.45/1.53  #Strategies tried      : 1
% 3.45/1.53  
% 3.45/1.53  Timing (in seconds)
% 3.45/1.53  ----------------------
% 3.45/1.54  Preprocessing        : 0.29
% 3.45/1.54  Parsing              : 0.16
% 3.45/1.54  CNF conversion       : 0.02
% 3.45/1.54  Main loop            : 0.48
% 3.45/1.54  Inferencing          : 0.18
% 3.45/1.54  Reduction            : 0.10
% 3.45/1.54  Demodulation         : 0.07
% 3.45/1.54  BG Simplification    : 0.02
% 3.45/1.54  Subsumption          : 0.15
% 3.45/1.54  Abstraction          : 0.02
% 3.45/1.54  MUC search           : 0.00
% 3.45/1.54  Cooper               : 0.00
% 3.45/1.54  Total                : 0.79
% 3.45/1.54  Index Insertion      : 0.00
% 3.45/1.54  Index Deletion       : 0.00
% 3.45/1.54  Index Matching       : 0.00
% 3.45/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
