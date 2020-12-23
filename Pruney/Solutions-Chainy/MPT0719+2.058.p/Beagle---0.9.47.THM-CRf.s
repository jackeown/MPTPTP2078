%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:50 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   52 (  91 expanded)
%              Number of leaves         :   24 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 187 expanded)
%              Number of equality atoms :   20 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

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

tff(c_158,plain,(
    ! [A_40,C_41,B_42] :
      ( ~ r2_hidden(A_40,C_41)
      | ~ r1_xboole_0(k2_tarski(A_40,B_42),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_163,plain,(
    ! [A_40] : ~ r2_hidden(A_40,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_158])).

tff(c_24,plain,(
    ! [A_18,B_19] : k1_relat_1('#skF_2'(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_18,B_19] : v1_relat_1('#skF_2'(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_64,plain,(
    ! [A_34] :
      ( k1_relat_1(A_34) != k1_xboole_0
      | k1_xboole_0 = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,(
    ! [A_18,B_19] :
      ( k1_relat_1('#skF_2'(A_18,B_19)) != k1_xboole_0
      | '#skF_2'(A_18,B_19) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_76,plain,(
    ! [A_35,B_36] :
      ( k1_xboole_0 != A_35
      | '#skF_2'(A_35,B_36) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_67])).

tff(c_84,plain,(
    ! [A_35] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_35 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_28])).

tff(c_93,plain,(
    ! [A_35] : k1_xboole_0 != A_35 ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_8,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_8])).

tff(c_109,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_funct_1('#skF_2'(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_86,plain,(
    ! [A_35] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_35 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_26])).

tff(c_117,plain,(
    ! [A_35] : k1_xboole_0 != A_35 ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_8])).

tff(c_140,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_183,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),k1_relat_1(B_50))
      | v5_funct_1(B_50,A_49)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_189,plain,(
    ! [A_49] :
      ( r2_hidden('#skF_1'(A_49,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_49)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_183])).

tff(c_193,plain,(
    ! [A_49] :
      ( r2_hidden('#skF_1'(A_49,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_140,c_189])).

tff(c_195,plain,(
    ! [A_51] :
      ( v5_funct_1(k1_xboole_0,A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_193])).

tff(c_30,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_198,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_195,c_30])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.24  
% 1.96/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.24  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.96/1.24  
% 1.96/1.24  %Foreground sorts:
% 1.96/1.24  
% 1.96/1.24  
% 1.96/1.24  %Background operators:
% 1.96/1.24  
% 1.96/1.24  
% 1.96/1.24  %Foreground operators:
% 1.96/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.24  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.96/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.96/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.96/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.24  
% 2.03/1.25  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.03/1.25  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.03/1.25  tff(f_34, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.03/1.25  tff(f_73, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 2.03/1.25  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.03/1.25  tff(f_37, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.03/1.25  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.03/1.25  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.03/1.25  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.03/1.25  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.25  tff(c_158, plain, (![A_40, C_41, B_42]: (~r2_hidden(A_40, C_41) | ~r1_xboole_0(k2_tarski(A_40, B_42), C_41))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.03/1.25  tff(c_163, plain, (![A_40]: (~r2_hidden(A_40, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_158])).
% 2.03/1.25  tff(c_24, plain, (![A_18, B_19]: (k1_relat_1('#skF_2'(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.03/1.25  tff(c_28, plain, (![A_18, B_19]: (v1_relat_1('#skF_2'(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.03/1.25  tff(c_64, plain, (![A_34]: (k1_relat_1(A_34)!=k1_xboole_0 | k1_xboole_0=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.03/1.25  tff(c_67, plain, (![A_18, B_19]: (k1_relat_1('#skF_2'(A_18, B_19))!=k1_xboole_0 | '#skF_2'(A_18, B_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_64])).
% 2.03/1.25  tff(c_76, plain, (![A_35, B_36]: (k1_xboole_0!=A_35 | '#skF_2'(A_35, B_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_67])).
% 2.03/1.25  tff(c_84, plain, (![A_35]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_35)), inference(superposition, [status(thm), theory('equality')], [c_76, c_28])).
% 2.03/1.25  tff(c_93, plain, (![A_35]: (k1_xboole_0!=A_35)), inference(splitLeft, [status(thm)], [c_84])).
% 2.03/1.25  tff(c_8, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.03/1.25  tff(c_108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_8])).
% 2.03/1.25  tff(c_109, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_84])).
% 2.03/1.25  tff(c_26, plain, (![A_18, B_19]: (v1_funct_1('#skF_2'(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.03/1.25  tff(c_86, plain, (![A_35]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_35)), inference(superposition, [status(thm), theory('equality')], [c_76, c_26])).
% 2.03/1.25  tff(c_117, plain, (![A_35]: (k1_xboole_0!=A_35)), inference(splitLeft, [status(thm)], [c_86])).
% 2.03/1.25  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_8])).
% 2.03/1.25  tff(c_140, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_86])).
% 2.03/1.25  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.03/1.25  tff(c_183, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), k1_relat_1(B_50)) | v5_funct_1(B_50, A_49) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.25  tff(c_189, plain, (![A_49]: (r2_hidden('#skF_1'(A_49, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_49) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_10, c_183])).
% 2.03/1.25  tff(c_193, plain, (![A_49]: (r2_hidden('#skF_1'(A_49, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_140, c_189])).
% 2.03/1.25  tff(c_195, plain, (![A_51]: (v5_funct_1(k1_xboole_0, A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(negUnitSimplification, [status(thm)], [c_163, c_193])).
% 2.03/1.25  tff(c_30, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.03/1.25  tff(c_198, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_195, c_30])).
% 2.03/1.25  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_198])).
% 2.03/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.25  
% 2.03/1.25  Inference rules
% 2.03/1.25  ----------------------
% 2.03/1.25  #Ref     : 0
% 2.03/1.25  #Sup     : 32
% 2.03/1.25  #Fact    : 0
% 2.03/1.25  #Define  : 0
% 2.03/1.25  #Split   : 4
% 2.03/1.25  #Chain   : 0
% 2.03/1.25  #Close   : 0
% 2.03/1.25  
% 2.03/1.25  Ordering : KBO
% 2.03/1.25  
% 2.03/1.25  Simplification rules
% 2.03/1.25  ----------------------
% 2.03/1.25  #Subsume      : 9
% 2.03/1.25  #Demod        : 12
% 2.03/1.25  #Tautology    : 16
% 2.03/1.25  #SimpNegUnit  : 11
% 2.03/1.25  #BackRed      : 4
% 2.03/1.25  
% 2.03/1.25  #Partial instantiations: 0
% 2.03/1.25  #Strategies tried      : 1
% 2.03/1.25  
% 2.03/1.25  Timing (in seconds)
% 2.03/1.25  ----------------------
% 2.03/1.26  Preprocessing        : 0.31
% 2.03/1.26  Parsing              : 0.17
% 2.03/1.26  CNF conversion       : 0.02
% 2.03/1.26  Main loop            : 0.15
% 2.03/1.26  Inferencing          : 0.06
% 2.03/1.26  Reduction            : 0.05
% 2.03/1.26  Demodulation         : 0.03
% 2.03/1.26  BG Simplification    : 0.01
% 2.03/1.26  Subsumption          : 0.02
% 2.03/1.26  Abstraction          : 0.01
% 2.03/1.26  MUC search           : 0.00
% 2.03/1.26  Cooper               : 0.00
% 2.03/1.26  Total                : 0.48
% 2.03/1.26  Index Insertion      : 0.00
% 2.03/1.26  Index Deletion       : 0.00
% 2.03/1.26  Index Matching       : 0.00
% 2.03/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
