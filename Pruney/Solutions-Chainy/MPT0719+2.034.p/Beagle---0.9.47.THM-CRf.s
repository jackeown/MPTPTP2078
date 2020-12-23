%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:47 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  71 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_48,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [A_37,B_38] : ~ r2_hidden(A_37,k2_zfmisc_1(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_70])).

tff(c_78,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_1'(A_40),A_40)
      | v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_83,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_78,c_76])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_43,plain,(
    ! [A_34] :
      ( v1_funct_1(A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_47,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_111,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_4'(A_51,B_52),k1_relat_1(B_52))
      | v5_funct_1(B_52,A_51)
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_114,plain,(
    ! [A_51] :
      ( r2_hidden('#skF_4'(A_51,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_51)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_111])).

tff(c_116,plain,(
    ! [A_51] :
      ( r2_hidden('#skF_4'(A_51,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_47,c_114])).

tff(c_118,plain,(
    ! [A_53] :
      ( v5_funct_1(k1_xboole_0,A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_116])).

tff(c_30,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_121,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_118,c_30])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:56:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.17  
% 1.68/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.17  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.68/1.17  
% 1.68/1.17  %Foreground sorts:
% 1.68/1.17  
% 1.68/1.17  
% 1.68/1.17  %Background operators:
% 1.68/1.17  
% 1.68/1.17  
% 1.68/1.17  %Foreground operators:
% 1.68/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.68/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.68/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.68/1.17  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.68/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.68/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.68/1.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.68/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.68/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.68/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.68/1.17  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.68/1.17  
% 1.87/1.18  tff(f_75, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 1.87/1.18  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.87/1.18  tff(f_35, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.87/1.18  tff(f_45, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.87/1.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.87/1.18  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.87/1.18  tff(f_48, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.87/1.18  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 1.87/1.18  tff(c_34, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.87/1.18  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.87/1.18  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.18  tff(c_70, plain, (![A_37, B_38]: (~r2_hidden(A_37, k2_zfmisc_1(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.18  tff(c_76, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_70])).
% 1.87/1.18  tff(c_78, plain, (![A_40]: (r2_hidden('#skF_1'(A_40), A_40) | v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.87/1.18  tff(c_83, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_76])).
% 1.87/1.18  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.87/1.18  tff(c_43, plain, (![A_34]: (v1_funct_1(A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.87/1.18  tff(c_47, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_43])).
% 1.87/1.18  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.87/1.18  tff(c_111, plain, (![A_51, B_52]: (r2_hidden('#skF_4'(A_51, B_52), k1_relat_1(B_52)) | v5_funct_1(B_52, A_51) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.87/1.18  tff(c_114, plain, (![A_51]: (r2_hidden('#skF_4'(A_51, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_51) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_20, c_111])).
% 1.87/1.18  tff(c_116, plain, (![A_51]: (r2_hidden('#skF_4'(A_51, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_47, c_114])).
% 1.87/1.18  tff(c_118, plain, (![A_53]: (v5_funct_1(k1_xboole_0, A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(negUnitSimplification, [status(thm)], [c_76, c_116])).
% 1.87/1.18  tff(c_30, plain, (~v5_funct_1(k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.87/1.18  tff(c_121, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_118, c_30])).
% 1.87/1.18  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_121])).
% 1.87/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  Inference rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Ref     : 1
% 1.87/1.18  #Sup     : 21
% 1.87/1.18  #Fact    : 0
% 1.87/1.18  #Define  : 0
% 1.87/1.18  #Split   : 0
% 1.87/1.18  #Chain   : 0
% 1.87/1.18  #Close   : 0
% 1.87/1.18  
% 1.87/1.18  Ordering : KBO
% 1.87/1.18  
% 1.87/1.18  Simplification rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Subsume      : 1
% 1.87/1.18  #Demod        : 4
% 1.87/1.18  #Tautology    : 14
% 1.87/1.18  #SimpNegUnit  : 1
% 1.87/1.18  #BackRed      : 0
% 1.87/1.18  
% 1.87/1.18  #Partial instantiations: 0
% 1.87/1.18  #Strategies tried      : 1
% 1.87/1.18  
% 1.87/1.18  Timing (in seconds)
% 1.87/1.18  ----------------------
% 1.87/1.18  Preprocessing        : 0.29
% 1.87/1.18  Parsing              : 0.16
% 1.87/1.18  CNF conversion       : 0.02
% 1.87/1.18  Main loop            : 0.12
% 1.87/1.18  Inferencing          : 0.05
% 1.87/1.18  Reduction            : 0.04
% 1.87/1.18  Demodulation         : 0.03
% 1.87/1.18  BG Simplification    : 0.01
% 1.87/1.18  Subsumption          : 0.02
% 1.87/1.18  Abstraction          : 0.01
% 1.87/1.18  MUC search           : 0.00
% 1.87/1.18  Cooper               : 0.00
% 1.87/1.18  Total                : 0.44
% 1.87/1.19  Index Insertion      : 0.00
% 1.87/1.19  Index Deletion       : 0.00
% 1.87/1.19  Index Matching       : 0.00
% 1.87/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
