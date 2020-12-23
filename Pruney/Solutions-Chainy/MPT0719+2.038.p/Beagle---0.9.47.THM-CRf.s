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
% DateTime   : Thu Dec  3 10:05:48 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   47 (  52 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  72 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_41,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_40,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_61,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,(
    ! [A_24,B_25] :
      ( v1_xboole_0(k2_zfmisc_1(A_24,B_25))
      | ~ v1_xboole_0(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_79,plain,(
    ! [A_28,B_29] :
      ( k2_zfmisc_1(A_28,B_29) = k1_xboole_0
      | ~ v1_xboole_0(B_29) ) ),
    inference(resolution,[status(thm)],[c_64,c_4])).

tff(c_86,plain,(
    ! [A_30] : k2_zfmisc_1(A_30,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_8,plain,(
    ! [A_4,B_5] : ~ r2_hidden(A_4,k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_30] : ~ r2_hidden(A_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_8])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_37,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_24])).

tff(c_26,plain,(
    ! [A_17] : v1_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_39,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_1'(A_26,B_27),k1_relat_1(B_27))
      | v5_funct_1(B_27,A_26)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_26)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_73])).

tff(c_78,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_39,c_76])).

tff(c_143,plain,(
    ! [A_40] :
      ( v5_funct_1(k1_xboole_0,A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_78])).

tff(c_28,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_146,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_143,c_28])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.23  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.93/1.23  
% 1.93/1.23  %Foreground sorts:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Background operators:
% 1.93/1.23  
% 1.93/1.23  
% 1.93/1.23  %Foreground operators:
% 1.93/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.23  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.93/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.93/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.93/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.23  
% 1.93/1.24  tff(f_72, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.93/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.93/1.24  tff(f_34, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 1.93/1.24  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.93/1.24  tff(f_37, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.93/1.24  tff(f_41, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.93/1.24  tff(f_65, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.93/1.24  tff(f_40, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.93/1.24  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.93/1.24  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.24  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.93/1.24  tff(c_64, plain, (![A_24, B_25]: (v1_xboole_0(k2_zfmisc_1(A_24, B_25)) | ~v1_xboole_0(B_25))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.24  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.93/1.24  tff(c_79, plain, (![A_28, B_29]: (k2_zfmisc_1(A_28, B_29)=k1_xboole_0 | ~v1_xboole_0(B_29))), inference(resolution, [status(thm)], [c_64, c_4])).
% 1.93/1.24  tff(c_86, plain, (![A_30]: (k2_zfmisc_1(A_30, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_79])).
% 1.93/1.24  tff(c_8, plain, (![A_4, B_5]: (~r2_hidden(A_4, k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.24  tff(c_94, plain, (![A_30]: (~r2_hidden(A_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_86, c_8])).
% 1.93/1.24  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.24  tff(c_24, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.24  tff(c_37, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_24])).
% 1.93/1.24  tff(c_26, plain, (![A_17]: (v1_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.24  tff(c_39, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_26])).
% 1.93/1.24  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.93/1.24  tff(c_73, plain, (![A_26, B_27]: (r2_hidden('#skF_1'(A_26, B_27), k1_relat_1(B_27)) | v5_funct_1(B_27, A_26) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.24  tff(c_76, plain, (![A_26]: (r2_hidden('#skF_1'(A_26, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_26) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_12, c_73])).
% 1.93/1.24  tff(c_78, plain, (![A_26]: (r2_hidden('#skF_1'(A_26, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_39, c_76])).
% 1.93/1.24  tff(c_143, plain, (![A_40]: (v5_funct_1(k1_xboole_0, A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(negUnitSimplification, [status(thm)], [c_94, c_78])).
% 1.93/1.24  tff(c_28, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.24  tff(c_146, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_143, c_28])).
% 1.93/1.24  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_146])).
% 1.93/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.24  
% 1.93/1.24  Inference rules
% 1.93/1.24  ----------------------
% 1.93/1.24  #Ref     : 0
% 1.93/1.24  #Sup     : 29
% 1.93/1.24  #Fact    : 0
% 1.93/1.24  #Define  : 0
% 1.93/1.24  #Split   : 0
% 1.93/1.24  #Chain   : 0
% 1.93/1.24  #Close   : 0
% 1.93/1.24  
% 1.93/1.24  Ordering : KBO
% 1.93/1.24  
% 1.93/1.24  Simplification rules
% 1.93/1.24  ----------------------
% 1.93/1.24  #Subsume      : 1
% 1.93/1.24  #Demod        : 15
% 1.93/1.24  #Tautology    : 19
% 1.93/1.24  #SimpNegUnit  : 1
% 1.93/1.24  #BackRed      : 0
% 1.93/1.24  
% 1.93/1.24  #Partial instantiations: 0
% 1.93/1.24  #Strategies tried      : 1
% 1.93/1.24  
% 1.93/1.24  Timing (in seconds)
% 1.93/1.24  ----------------------
% 1.93/1.25  Preprocessing        : 0.28
% 1.93/1.25  Parsing              : 0.17
% 1.93/1.25  CNF conversion       : 0.02
% 1.93/1.25  Main loop            : 0.14
% 1.93/1.25  Inferencing          : 0.06
% 1.93/1.25  Reduction            : 0.04
% 1.93/1.25  Demodulation         : 0.03
% 1.93/1.25  BG Simplification    : 0.01
% 1.93/1.25  Subsumption          : 0.02
% 1.93/1.25  Abstraction          : 0.01
% 1.93/1.25  MUC search           : 0.00
% 1.93/1.25  Cooper               : 0.00
% 1.93/1.25  Total                : 0.45
% 1.93/1.25  Index Insertion      : 0.00
% 1.93/1.25  Index Deletion       : 0.00
% 1.93/1.25  Index Matching       : 0.00
% 1.93/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
