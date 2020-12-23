%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:51 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   51 (  91 expanded)
%              Number of leaves         :   24 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 187 expanded)
%              Number of equality atoms :   19 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_37,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_150,plain,(
    ! [A_36,C_37,B_38] :
      ( ~ r2_hidden(A_36,C_37)
      | ~ r1_xboole_0(k2_tarski(A_36,B_38),C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_155,plain,(
    ! [A_36] : ~ r2_hidden(A_36,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_150])).

tff(c_24,plain,(
    ! [A_18] : k1_relat_1('#skF_2'(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_18] : v1_relat_1('#skF_2'(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_64,plain,(
    ! [A_30] :
      ( k1_relat_1(A_30) != k1_xboole_0
      | k1_xboole_0 = A_30
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,(
    ! [A_18] :
      ( k1_relat_1('#skF_2'(A_18)) != k1_xboole_0
      | '#skF_2'(A_18) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_75,plain,(
    ! [A_31] :
      ( k1_xboole_0 != A_31
      | '#skF_2'(A_31) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_67])).

tff(c_85,plain,(
    ! [A_31] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_31 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_28])).

tff(c_108,plain,(
    ! [A_31] : k1_xboole_0 != A_31 ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_10])).

tff(c_115,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_26,plain,(
    ! [A_18] : v1_funct_1('#skF_2'(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_83,plain,(
    ! [A_31] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_31 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_26])).

tff(c_92,plain,(
    ! [A_31] : k1_xboole_0 != A_31 ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_10])).

tff(c_98,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_159,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),k1_relat_1(B_43))
      | v5_funct_1(B_43,A_42)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_168,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_42)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_159])).

tff(c_173,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_98,c_168])).

tff(c_191,plain,(
    ! [A_47] :
      ( v5_funct_1(k1_xboole_0,A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_173])).

tff(c_30,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_194,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_191,c_30])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:02:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.32  
% 2.06/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.32  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.06/1.32  
% 2.06/1.32  %Foreground sorts:
% 2.06/1.32  
% 2.06/1.32  
% 2.06/1.32  %Background operators:
% 2.06/1.32  
% 2.06/1.32  
% 2.06/1.32  %Foreground operators:
% 2.06/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.32  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.06/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.32  
% 2.06/1.33  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.06/1.33  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.06/1.33  tff(f_34, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.06/1.33  tff(f_73, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 2.06/1.33  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.06/1.33  tff(f_37, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.06/1.33  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.06/1.33  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.06/1.33  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.06/1.33  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.33  tff(c_150, plain, (![A_36, C_37, B_38]: (~r2_hidden(A_36, C_37) | ~r1_xboole_0(k2_tarski(A_36, B_38), C_37))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.33  tff(c_155, plain, (![A_36]: (~r2_hidden(A_36, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_150])).
% 2.06/1.33  tff(c_24, plain, (![A_18]: (k1_relat_1('#skF_2'(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.06/1.34  tff(c_28, plain, (![A_18]: (v1_relat_1('#skF_2'(A_18)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.06/1.34  tff(c_64, plain, (![A_30]: (k1_relat_1(A_30)!=k1_xboole_0 | k1_xboole_0=A_30 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.34  tff(c_67, plain, (![A_18]: (k1_relat_1('#skF_2'(A_18))!=k1_xboole_0 | '#skF_2'(A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_64])).
% 2.06/1.34  tff(c_75, plain, (![A_31]: (k1_xboole_0!=A_31 | '#skF_2'(A_31)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_67])).
% 2.06/1.34  tff(c_85, plain, (![A_31]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_31)), inference(superposition, [status(thm), theory('equality')], [c_75, c_28])).
% 2.06/1.34  tff(c_108, plain, (![A_31]: (k1_xboole_0!=A_31)), inference(splitLeft, [status(thm)], [c_85])).
% 2.06/1.34  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.34  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_10])).
% 2.06/1.34  tff(c_115, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_85])).
% 2.06/1.34  tff(c_26, plain, (![A_18]: (v1_funct_1('#skF_2'(A_18)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.06/1.34  tff(c_83, plain, (![A_31]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_31)), inference(superposition, [status(thm), theory('equality')], [c_75, c_26])).
% 2.06/1.34  tff(c_92, plain, (![A_31]: (k1_xboole_0!=A_31)), inference(splitLeft, [status(thm)], [c_83])).
% 2.06/1.34  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_10])).
% 2.06/1.34  tff(c_98, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_83])).
% 2.06/1.34  tff(c_159, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), k1_relat_1(B_43)) | v5_funct_1(B_43, A_42) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.34  tff(c_168, plain, (![A_42]: (r2_hidden('#skF_1'(A_42, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_42) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_10, c_159])).
% 2.06/1.34  tff(c_173, plain, (![A_42]: (r2_hidden('#skF_1'(A_42, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_98, c_168])).
% 2.06/1.34  tff(c_191, plain, (![A_47]: (v5_funct_1(k1_xboole_0, A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(negUnitSimplification, [status(thm)], [c_155, c_173])).
% 2.06/1.34  tff(c_30, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.06/1.34  tff(c_194, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_191, c_30])).
% 2.06/1.34  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_194])).
% 2.06/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.34  
% 2.06/1.34  Inference rules
% 2.06/1.34  ----------------------
% 2.06/1.34  #Ref     : 0
% 2.06/1.34  #Sup     : 31
% 2.06/1.34  #Fact    : 0
% 2.06/1.34  #Define  : 0
% 2.06/1.34  #Split   : 4
% 2.06/1.34  #Chain   : 0
% 2.06/1.34  #Close   : 0
% 2.06/1.34  
% 2.06/1.34  Ordering : KBO
% 2.06/1.34  
% 2.06/1.34  Simplification rules
% 2.06/1.34  ----------------------
% 2.06/1.34  #Subsume      : 6
% 2.06/1.34  #Demod        : 16
% 2.06/1.34  #Tautology    : 15
% 2.06/1.34  #SimpNegUnit  : 11
% 2.06/1.34  #BackRed      : 4
% 2.06/1.34  
% 2.06/1.34  #Partial instantiations: 0
% 2.06/1.34  #Strategies tried      : 1
% 2.06/1.34  
% 2.06/1.34  Timing (in seconds)
% 2.06/1.34  ----------------------
% 2.06/1.34  Preprocessing        : 0.38
% 2.06/1.34  Parsing              : 0.22
% 2.06/1.34  CNF conversion       : 0.03
% 2.06/1.34  Main loop            : 0.18
% 2.06/1.34  Inferencing          : 0.07
% 2.06/1.34  Reduction            : 0.06
% 2.06/1.34  Demodulation         : 0.04
% 2.06/1.34  BG Simplification    : 0.01
% 2.06/1.34  Subsumption          : 0.03
% 2.06/1.34  Abstraction          : 0.01
% 2.06/1.34  MUC search           : 0.00
% 2.06/1.34  Cooper               : 0.00
% 2.06/1.34  Total                : 0.59
% 2.06/1.34  Index Insertion      : 0.00
% 2.06/1.34  Index Deletion       : 0.00
% 2.06/1.34  Index Matching       : 0.00
% 2.06/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
