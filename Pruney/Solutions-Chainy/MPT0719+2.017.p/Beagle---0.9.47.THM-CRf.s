%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:45 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   45 (  51 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 (  74 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_44,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_64,axiom,(
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

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_54,plain,(
    ! [A_23,B_24] :
      ( v1_xboole_0(k2_zfmisc_1(A_23,B_24))
      | ~ v1_xboole_0(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_75,plain,(
    ! [A_31,B_32] :
      ( k2_zfmisc_1(A_31,B_32) = k1_xboole_0
      | ~ v1_xboole_0(B_32) ) ),
    inference(resolution,[status(thm)],[c_54,c_4])).

tff(c_82,plain,(
    ! [A_33] : k2_zfmisc_1(A_33,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_75])).

tff(c_8,plain,(
    ! [A_4,B_5] : ~ r2_hidden(A_4,k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [A_33] : ~ r2_hidden(A_33,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8])).

tff(c_48,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_48])).

tff(c_43,plain,(
    ! [A_19] :
      ( v1_funct_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_69,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),k1_relat_1(B_30))
      | v5_funct_1(B_30,A_29)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_1'(A_29,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_29)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_69])).

tff(c_74,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_1'(A_29,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_47,c_72])).

tff(c_147,plain,(
    ! [A_40] :
      ( v5_funct_1(k1_xboole_0,A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_74])).

tff(c_24,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_150,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_147,c_24])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:33:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.25  
% 1.98/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.25  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.98/1.25  
% 1.98/1.25  %Foreground sorts:
% 1.98/1.25  
% 1.98/1.25  
% 1.98/1.25  %Background operators:
% 1.98/1.25  
% 1.98/1.25  
% 1.98/1.25  %Foreground operators:
% 1.98/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.25  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.98/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.98/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.25  
% 1.98/1.27  tff(f_71, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 1.98/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.98/1.27  tff(f_34, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 1.98/1.27  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.98/1.27  tff(f_37, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.98/1.27  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.98/1.27  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.98/1.27  tff(f_44, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.98/1.27  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 1.98/1.27  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.98/1.27  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.98/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.98/1.27  tff(c_54, plain, (![A_23, B_24]: (v1_xboole_0(k2_zfmisc_1(A_23, B_24)) | ~v1_xboole_0(B_24))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.98/1.27  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.98/1.27  tff(c_75, plain, (![A_31, B_32]: (k2_zfmisc_1(A_31, B_32)=k1_xboole_0 | ~v1_xboole_0(B_32))), inference(resolution, [status(thm)], [c_54, c_4])).
% 1.98/1.27  tff(c_82, plain, (![A_33]: (k2_zfmisc_1(A_33, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_75])).
% 1.98/1.27  tff(c_8, plain, (![A_4, B_5]: (~r2_hidden(A_4, k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.98/1.27  tff(c_96, plain, (![A_33]: (~r2_hidden(A_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_82, c_8])).
% 1.98/1.27  tff(c_48, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.27  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_48])).
% 1.98/1.27  tff(c_43, plain, (![A_19]: (v1_funct_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.98/1.27  tff(c_47, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_43])).
% 1.98/1.27  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.98/1.27  tff(c_69, plain, (![A_29, B_30]: (r2_hidden('#skF_1'(A_29, B_30), k1_relat_1(B_30)) | v5_funct_1(B_30, A_29) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.98/1.27  tff(c_72, plain, (![A_29]: (r2_hidden('#skF_1'(A_29, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_29) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_14, c_69])).
% 1.98/1.27  tff(c_74, plain, (![A_29]: (r2_hidden('#skF_1'(A_29, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_47, c_72])).
% 1.98/1.27  tff(c_147, plain, (![A_40]: (v5_funct_1(k1_xboole_0, A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(negUnitSimplification, [status(thm)], [c_96, c_74])).
% 1.98/1.27  tff(c_24, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.98/1.27  tff(c_150, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_147, c_24])).
% 1.98/1.27  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_150])).
% 1.98/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.27  
% 1.98/1.27  Inference rules
% 1.98/1.27  ----------------------
% 1.98/1.27  #Ref     : 0
% 1.98/1.27  #Sup     : 29
% 1.98/1.27  #Fact    : 0
% 1.98/1.27  #Define  : 0
% 1.98/1.27  #Split   : 0
% 1.98/1.27  #Chain   : 0
% 1.98/1.27  #Close   : 0
% 1.98/1.27  
% 1.98/1.27  Ordering : KBO
% 1.98/1.27  
% 1.98/1.27  Simplification rules
% 1.98/1.27  ----------------------
% 1.98/1.27  #Subsume      : 1
% 1.98/1.27  #Demod        : 17
% 1.98/1.27  #Tautology    : 18
% 1.98/1.27  #SimpNegUnit  : 1
% 1.98/1.27  #BackRed      : 0
% 1.98/1.27  
% 1.98/1.27  #Partial instantiations: 0
% 1.98/1.27  #Strategies tried      : 1
% 1.98/1.27  
% 1.98/1.27  Timing (in seconds)
% 1.98/1.28  ----------------------
% 1.98/1.28  Preprocessing        : 0.28
% 1.98/1.28  Parsing              : 0.16
% 1.98/1.28  CNF conversion       : 0.02
% 1.98/1.28  Main loop            : 0.21
% 1.98/1.28  Inferencing          : 0.10
% 1.98/1.28  Reduction            : 0.06
% 1.98/1.28  Demodulation         : 0.04
% 1.98/1.28  BG Simplification    : 0.01
% 1.98/1.28  Subsumption          : 0.03
% 1.98/1.28  Abstraction          : 0.01
% 1.98/1.28  MUC search           : 0.00
% 1.98/1.28  Cooper               : 0.00
% 1.98/1.28  Total                : 0.54
% 1.98/1.28  Index Insertion      : 0.00
% 1.98/1.28  Index Deletion       : 0.00
% 1.98/1.28  Index Matching       : 0.00
% 1.98/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
