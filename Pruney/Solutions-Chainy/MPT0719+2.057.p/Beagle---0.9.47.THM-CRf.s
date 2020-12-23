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
% DateTime   : Thu Dec  3 10:05:50 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   53 (  92 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 187 expanded)
%              Number of equality atoms :   20 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_tarski > k1_funct_1 > #nlpp > o_1_0_funct_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_1_0_funct_1,type,(
    o_1_0_funct_1: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = B
      & ! [D] :
          ( r2_hidden(D,B)
         => k1_funct_1(C,D) = o_1_0_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_37,axiom,
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

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_123,plain,(
    ! [A_36,C_37,B_38] :
      ( ~ r2_hidden(A_36,C_37)
      | ~ r1_xboole_0(k2_tarski(A_36,B_38),C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_128,plain,(
    ! [A_36] : ~ r2_hidden(A_36,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_123])).

tff(c_24,plain,(
    ! [A_18,B_19] : k1_relat_1('#skF_2'(A_18,B_19)) = B_19 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_18,B_19] : v1_relat_1('#skF_2'(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_55,plain,(
    ! [A_32] :
      ( k1_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [A_18,B_19] :
      ( k1_relat_1('#skF_2'(A_18,B_19)) != k1_xboole_0
      | '#skF_2'(A_18,B_19) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_67,plain,(
    ! [B_33,A_34] :
      ( k1_xboole_0 != B_33
      | '#skF_2'(A_34,B_33) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_58])).

tff(c_75,plain,(
    ! [B_33] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != B_33 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_28])).

tff(c_84,plain,(
    ! [B_33] : k1_xboole_0 != B_33 ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_8,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_8])).

tff(c_90,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_funct_1('#skF_2'(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_77,plain,(
    ! [B_33] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != B_33 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_26])).

tff(c_114,plain,(
    ! [B_33] : k1_xboole_0 != B_33 ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_8])).

tff(c_121,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_159,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_1'(A_50,B_51),k1_relat_1(B_51))
      | v5_funct_1(B_51,A_50)
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_167,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_1'(A_50,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_50)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_159])).

tff(c_172,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_1'(A_50,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_121,c_167])).

tff(c_187,plain,(
    ! [A_54] :
      ( v5_funct_1(k1_xboole_0,A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_172])).

tff(c_30,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_190,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_30])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:36:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.24  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_tarski > k1_funct_1 > #nlpp > o_1_0_funct_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.95/1.24  
% 1.95/1.24  %Foreground sorts:
% 1.95/1.24  
% 1.95/1.24  
% 1.95/1.24  %Background operators:
% 1.95/1.24  
% 1.95/1.24  
% 1.95/1.24  %Foreground operators:
% 1.95/1.24  tff(o_1_0_funct_1, type, o_1_0_funct_1: $i > $i).
% 1.95/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.24  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.95/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.95/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.95/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.95/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.25  
% 1.95/1.26  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.95/1.26  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.95/1.26  tff(f_34, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.95/1.26  tff(f_73, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = B)) & (![D]: (r2_hidden(D, B) => (k1_funct_1(C, D) = o_1_0_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e1_27_1__funct_1)).
% 1.95/1.26  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.95/1.26  tff(f_37, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.95/1.26  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.95/1.26  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.95/1.26  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.95/1.26  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.26  tff(c_123, plain, (![A_36, C_37, B_38]: (~r2_hidden(A_36, C_37) | ~r1_xboole_0(k2_tarski(A_36, B_38), C_37))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.95/1.26  tff(c_128, plain, (![A_36]: (~r2_hidden(A_36, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_123])).
% 1.95/1.26  tff(c_24, plain, (![A_18, B_19]: (k1_relat_1('#skF_2'(A_18, B_19))=B_19)), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.95/1.26  tff(c_28, plain, (![A_18, B_19]: (v1_relat_1('#skF_2'(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.95/1.26  tff(c_55, plain, (![A_32]: (k1_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.26  tff(c_58, plain, (![A_18, B_19]: (k1_relat_1('#skF_2'(A_18, B_19))!=k1_xboole_0 | '#skF_2'(A_18, B_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_55])).
% 1.95/1.26  tff(c_67, plain, (![B_33, A_34]: (k1_xboole_0!=B_33 | '#skF_2'(A_34, B_33)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_58])).
% 1.95/1.26  tff(c_75, plain, (![B_33]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=B_33)), inference(superposition, [status(thm), theory('equality')], [c_67, c_28])).
% 1.95/1.26  tff(c_84, plain, (![B_33]: (k1_xboole_0!=B_33)), inference(splitLeft, [status(thm)], [c_75])).
% 1.95/1.26  tff(c_8, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.26  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_8])).
% 1.95/1.26  tff(c_90, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_75])).
% 1.95/1.26  tff(c_26, plain, (![A_18, B_19]: (v1_funct_1('#skF_2'(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.95/1.26  tff(c_77, plain, (![B_33]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=B_33)), inference(superposition, [status(thm), theory('equality')], [c_67, c_26])).
% 1.95/1.26  tff(c_114, plain, (![B_33]: (k1_xboole_0!=B_33)), inference(splitLeft, [status(thm)], [c_77])).
% 1.95/1.26  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_8])).
% 1.95/1.26  tff(c_121, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_77])).
% 1.95/1.26  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.26  tff(c_159, plain, (![A_50, B_51]: (r2_hidden('#skF_1'(A_50, B_51), k1_relat_1(B_51)) | v5_funct_1(B_51, A_50) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.26  tff(c_167, plain, (![A_50]: (r2_hidden('#skF_1'(A_50, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_50) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_10, c_159])).
% 1.95/1.26  tff(c_172, plain, (![A_50]: (r2_hidden('#skF_1'(A_50, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_121, c_167])).
% 1.95/1.26  tff(c_187, plain, (![A_54]: (v5_funct_1(k1_xboole_0, A_54) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(negUnitSimplification, [status(thm)], [c_128, c_172])).
% 1.95/1.26  tff(c_30, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.95/1.26  tff(c_190, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_187, c_30])).
% 1.95/1.26  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_190])).
% 1.95/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.26  
% 1.95/1.26  Inference rules
% 1.95/1.26  ----------------------
% 1.95/1.26  #Ref     : 0
% 1.95/1.26  #Sup     : 30
% 1.95/1.26  #Fact    : 0
% 1.95/1.26  #Define  : 0
% 1.95/1.26  #Split   : 4
% 1.95/1.26  #Chain   : 0
% 1.95/1.26  #Close   : 0
% 1.95/1.26  
% 1.95/1.26  Ordering : KBO
% 1.95/1.26  
% 1.95/1.26  Simplification rules
% 1.95/1.26  ----------------------
% 1.95/1.26  #Subsume      : 8
% 1.95/1.26  #Demod        : 15
% 1.95/1.26  #Tautology    : 15
% 1.95/1.26  #SimpNegUnit  : 10
% 1.95/1.26  #BackRed      : 4
% 1.95/1.26  
% 1.95/1.26  #Partial instantiations: 0
% 1.95/1.26  #Strategies tried      : 1
% 1.95/1.26  
% 1.95/1.26  Timing (in seconds)
% 1.95/1.26  ----------------------
% 1.95/1.26  Preprocessing        : 0.32
% 1.95/1.26  Parsing              : 0.18
% 1.95/1.26  CNF conversion       : 0.02
% 1.95/1.26  Main loop            : 0.15
% 1.95/1.26  Inferencing          : 0.06
% 1.95/1.26  Reduction            : 0.05
% 1.95/1.26  Demodulation         : 0.03
% 1.95/1.26  BG Simplification    : 0.01
% 1.95/1.26  Subsumption          : 0.03
% 1.95/1.26  Abstraction          : 0.01
% 1.95/1.26  MUC search           : 0.00
% 1.95/1.26  Cooper               : 0.00
% 1.95/1.26  Total                : 0.50
% 1.95/1.26  Index Insertion      : 0.00
% 1.95/1.26  Index Deletion       : 0.00
% 1.95/1.26  Index Matching       : 0.00
% 1.95/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
