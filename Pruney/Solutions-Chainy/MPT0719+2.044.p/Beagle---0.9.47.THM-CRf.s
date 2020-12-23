%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:49 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 285 expanded)
%              Number of leaves         :   31 ( 107 expanded)
%              Depth                    :   16
%              Number of atoms          :  129 ( 706 expanded)
%              Number of equality atoms :   53 ( 344 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_95,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_83,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_32,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    ! [A_24] : k1_relat_1('#skF_2'(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    ! [A_24] : v1_relat_1('#skF_2'(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_133,plain,(
    ! [A_41] :
      ( k1_relat_1(A_41) != k1_xboole_0
      | k1_xboole_0 = A_41
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_139,plain,(
    ! [A_24] :
      ( k1_relat_1('#skF_2'(A_24)) != k1_xboole_0
      | '#skF_2'(A_24) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_133])).

tff(c_145,plain,(
    ! [A_24] :
      ( k1_xboole_0 != A_24
      | '#skF_2'(A_24) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_139])).

tff(c_36,plain,(
    ! [A_24] : v1_funct_1('#skF_2'(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_462,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_1'(A_74,B_75),k1_relat_1(B_75))
      | v5_funct_1(B_75,A_74)
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_471,plain,(
    ! [A_74,A_24] :
      ( r2_hidden('#skF_1'(A_74,'#skF_2'(A_24)),A_24)
      | v5_funct_1('#skF_2'(A_24),A_74)
      | ~ v1_funct_1('#skF_2'(A_24))
      | ~ v1_relat_1('#skF_2'(A_24))
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_462])).

tff(c_527,plain,(
    ! [A_82,A_83] :
      ( r2_hidden('#skF_1'(A_82,'#skF_2'(A_83)),A_83)
      | v5_funct_1('#skF_2'(A_83),A_82)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_471])).

tff(c_149,plain,(
    ! [A_42] :
      ( k1_xboole_0 != A_42
      | '#skF_2'(A_42) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_139])).

tff(c_163,plain,(
    ! [A_42] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_42 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_38])).

tff(c_198,plain,(
    ! [A_42] : k1_xboole_0 != A_42 ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_57,plain,(
    ! [A_34] :
      ( k5_relat_1(A_34,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [A_24] : k5_relat_1('#skF_2'(A_24),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_57])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_68])).

tff(c_212,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_252,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_34])).

tff(c_263,plain,(
    ! [A_48] :
      ( k2_relat_1(A_48) = k1_xboole_0
      | k1_relat_1(A_48) != k1_xboole_0
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_266,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_212,c_263])).

tff(c_278,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_266])).

tff(c_357,plain,(
    ! [A_59,B_60] :
      ( k5_relat_1(k6_relat_1(A_59),B_60) = k7_relat_1(B_60,A_59)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_4] : k5_relat_1(k6_relat_1(A_4),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_57])).

tff(c_364,plain,(
    ! [A_59] :
      ( k7_relat_1(k1_xboole_0,A_59) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_67])).

tff(c_377,plain,(
    ! [A_61] : k7_relat_1(k1_xboole_0,A_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_364])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_382,plain,(
    ! [A_61] :
      ( k9_relat_1(k1_xboole_0,A_61) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_6])).

tff(c_396,plain,(
    ! [A_64] : k9_relat_1(k1_xboole_0,A_64) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_278,c_382])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k9_relat_1(A_1,k1_tarski(B_3)) = k11_relat_1(A_1,B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_402,plain,(
    ! [B_3] :
      ( k11_relat_1(k1_xboole_0,B_3) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_2])).

tff(c_411,plain,(
    ! [B_3] : k11_relat_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_402])).

tff(c_436,plain,(
    ! [B_68,A_69] :
      ( k11_relat_1(B_68,A_69) != k1_xboole_0
      | ~ r2_hidden(A_69,k1_relat_1(B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_442,plain,(
    ! [A_24,A_69] :
      ( k11_relat_1('#skF_2'(A_24),A_69) != k1_xboole_0
      | ~ r2_hidden(A_69,A_24)
      | ~ v1_relat_1('#skF_2'(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_436])).

tff(c_446,plain,(
    ! [A_70,A_71] :
      ( k11_relat_1('#skF_2'(A_70),A_71) != k1_xboole_0
      | ~ r2_hidden(A_71,A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_442])).

tff(c_452,plain,(
    ! [A_71,A_24] :
      ( k11_relat_1(k1_xboole_0,A_71) != k1_xboole_0
      | ~ r2_hidden(A_71,A_24)
      | k1_xboole_0 != A_24 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_446])).

tff(c_455,plain,(
    ! [A_71,A_24] :
      ( ~ r2_hidden(A_71,A_24)
      | k1_xboole_0 != A_24 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_452])).

tff(c_541,plain,(
    ! [A_84,A_85] :
      ( k1_xboole_0 != A_84
      | v5_funct_1('#skF_2'(A_84),A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_527,c_455])).

tff(c_544,plain,(
    ! [A_24,A_85] :
      ( k1_xboole_0 != A_24
      | v5_funct_1(k1_xboole_0,A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85)
      | k1_xboole_0 != A_24 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_541])).

tff(c_561,plain,(
    ! [A_24] :
      ( k1_xboole_0 != A_24
      | k1_xboole_0 != A_24 ) ),
    inference(splitLeft,[status(thm)],[c_544])).

tff(c_567,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_561])).

tff(c_569,plain,(
    ! [A_89] :
      ( v5_funct_1(k1_xboole_0,A_89)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(splitRight,[status(thm)],[c_544])).

tff(c_40,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_572,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_569,c_40])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_572])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.30  
% 2.38/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.30  %$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.38/1.30  
% 2.38/1.30  %Foreground sorts:
% 2.38/1.30  
% 2.38/1.30  
% 2.38/1.30  %Background operators:
% 2.38/1.30  
% 2.38/1.30  
% 2.38/1.30  %Foreground operators:
% 2.38/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.38/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.38/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.38/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.38/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.38/1.30  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.38/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.38/1.30  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.38/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.38/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.38/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.38/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.30  
% 2.38/1.31  tff(f_102, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.38/1.31  tff(f_95, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.38/1.31  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.38/1.31  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.38/1.31  tff(f_49, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.38/1.31  tff(f_63, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.38/1.31  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.38/1.31  tff(f_32, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.38/1.31  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.38/1.31  tff(f_30, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.38/1.31  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.38/1.31  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.38/1.31  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.38/1.31  tff(c_34, plain, (![A_24]: (k1_relat_1('#skF_2'(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.38/1.31  tff(c_38, plain, (![A_24]: (v1_relat_1('#skF_2'(A_24)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.38/1.31  tff(c_133, plain, (![A_41]: (k1_relat_1(A_41)!=k1_xboole_0 | k1_xboole_0=A_41 | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.38/1.31  tff(c_139, plain, (![A_24]: (k1_relat_1('#skF_2'(A_24))!=k1_xboole_0 | '#skF_2'(A_24)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_133])).
% 2.38/1.31  tff(c_145, plain, (![A_24]: (k1_xboole_0!=A_24 | '#skF_2'(A_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_139])).
% 2.38/1.31  tff(c_36, plain, (![A_24]: (v1_funct_1('#skF_2'(A_24)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.38/1.31  tff(c_462, plain, (![A_74, B_75]: (r2_hidden('#skF_1'(A_74, B_75), k1_relat_1(B_75)) | v5_funct_1(B_75, A_74) | ~v1_funct_1(B_75) | ~v1_relat_1(B_75) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.38/1.31  tff(c_471, plain, (![A_74, A_24]: (r2_hidden('#skF_1'(A_74, '#skF_2'(A_24)), A_24) | v5_funct_1('#skF_2'(A_24), A_74) | ~v1_funct_1('#skF_2'(A_24)) | ~v1_relat_1('#skF_2'(A_24)) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_34, c_462])).
% 2.38/1.31  tff(c_527, plain, (![A_82, A_83]: (r2_hidden('#skF_1'(A_82, '#skF_2'(A_83)), A_83) | v5_funct_1('#skF_2'(A_83), A_82) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_471])).
% 2.38/1.31  tff(c_149, plain, (![A_42]: (k1_xboole_0!=A_42 | '#skF_2'(A_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_139])).
% 2.38/1.31  tff(c_163, plain, (![A_42]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_42)), inference(superposition, [status(thm), theory('equality')], [c_149, c_38])).
% 2.38/1.31  tff(c_198, plain, (![A_42]: (k1_xboole_0!=A_42)), inference(splitLeft, [status(thm)], [c_163])).
% 2.38/1.31  tff(c_57, plain, (![A_34]: (k5_relat_1(A_34, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.31  tff(c_68, plain, (![A_24]: (k5_relat_1('#skF_2'(A_24), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_57])).
% 2.38/1.31  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_68])).
% 2.38/1.31  tff(c_212, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_163])).
% 2.38/1.31  tff(c_252, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_149, c_34])).
% 2.38/1.31  tff(c_263, plain, (![A_48]: (k2_relat_1(A_48)=k1_xboole_0 | k1_relat_1(A_48)!=k1_xboole_0 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.38/1.31  tff(c_266, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_212, c_263])).
% 2.38/1.31  tff(c_278, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_252, c_266])).
% 2.38/1.31  tff(c_357, plain, (![A_59, B_60]: (k5_relat_1(k6_relat_1(A_59), B_60)=k7_relat_1(B_60, A_59) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.38/1.31  tff(c_4, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.38/1.31  tff(c_67, plain, (![A_4]: (k5_relat_1(k6_relat_1(A_4), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_57])).
% 2.38/1.31  tff(c_364, plain, (![A_59]: (k7_relat_1(k1_xboole_0, A_59)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_357, c_67])).
% 2.38/1.31  tff(c_377, plain, (![A_61]: (k7_relat_1(k1_xboole_0, A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_212, c_364])).
% 2.38/1.31  tff(c_6, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.31  tff(c_382, plain, (![A_61]: (k9_relat_1(k1_xboole_0, A_61)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_377, c_6])).
% 2.38/1.31  tff(c_396, plain, (![A_64]: (k9_relat_1(k1_xboole_0, A_64)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_212, c_278, c_382])).
% 2.38/1.31  tff(c_2, plain, (![A_1, B_3]: (k9_relat_1(A_1, k1_tarski(B_3))=k11_relat_1(A_1, B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.38/1.31  tff(c_402, plain, (![B_3]: (k11_relat_1(k1_xboole_0, B_3)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_396, c_2])).
% 2.38/1.31  tff(c_411, plain, (![B_3]: (k11_relat_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_212, c_402])).
% 2.38/1.31  tff(c_436, plain, (![B_68, A_69]: (k11_relat_1(B_68, A_69)!=k1_xboole_0 | ~r2_hidden(A_69, k1_relat_1(B_68)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.31  tff(c_442, plain, (![A_24, A_69]: (k11_relat_1('#skF_2'(A_24), A_69)!=k1_xboole_0 | ~r2_hidden(A_69, A_24) | ~v1_relat_1('#skF_2'(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_436])).
% 2.38/1.31  tff(c_446, plain, (![A_70, A_71]: (k11_relat_1('#skF_2'(A_70), A_71)!=k1_xboole_0 | ~r2_hidden(A_71, A_70))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_442])).
% 2.38/1.31  tff(c_452, plain, (![A_71, A_24]: (k11_relat_1(k1_xboole_0, A_71)!=k1_xboole_0 | ~r2_hidden(A_71, A_24) | k1_xboole_0!=A_24)), inference(superposition, [status(thm), theory('equality')], [c_145, c_446])).
% 2.38/1.31  tff(c_455, plain, (![A_71, A_24]: (~r2_hidden(A_71, A_24) | k1_xboole_0!=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_411, c_452])).
% 2.38/1.31  tff(c_541, plain, (![A_84, A_85]: (k1_xboole_0!=A_84 | v5_funct_1('#skF_2'(A_84), A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_527, c_455])).
% 2.38/1.32  tff(c_544, plain, (![A_24, A_85]: (k1_xboole_0!=A_24 | v5_funct_1(k1_xboole_0, A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85) | k1_xboole_0!=A_24)), inference(superposition, [status(thm), theory('equality')], [c_145, c_541])).
% 2.38/1.32  tff(c_561, plain, (![A_24]: (k1_xboole_0!=A_24 | k1_xboole_0!=A_24)), inference(splitLeft, [status(thm)], [c_544])).
% 2.38/1.32  tff(c_567, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_561])).
% 2.38/1.32  tff(c_569, plain, (![A_89]: (v5_funct_1(k1_xboole_0, A_89) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(splitRight, [status(thm)], [c_544])).
% 2.38/1.32  tff(c_40, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.38/1.32  tff(c_572, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_569, c_40])).
% 2.38/1.32  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_572])).
% 2.38/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.32  
% 2.38/1.32  Inference rules
% 2.38/1.32  ----------------------
% 2.38/1.32  #Ref     : 2
% 2.38/1.32  #Sup     : 112
% 2.38/1.32  #Fact    : 0
% 2.38/1.32  #Define  : 0
% 2.38/1.32  #Split   : 5
% 2.38/1.32  #Chain   : 0
% 2.38/1.32  #Close   : 0
% 2.38/1.32  
% 2.38/1.32  Ordering : KBO
% 2.38/1.32  
% 2.38/1.32  Simplification rules
% 2.38/1.32  ----------------------
% 2.38/1.32  #Subsume      : 19
% 2.38/1.32  #Demod        : 37
% 2.38/1.32  #Tautology    : 64
% 2.38/1.32  #SimpNegUnit  : 26
% 2.38/1.32  #BackRed      : 16
% 2.38/1.32  
% 2.38/1.32  #Partial instantiations: 0
% 2.38/1.32  #Strategies tried      : 1
% 2.38/1.32  
% 2.38/1.32  Timing (in seconds)
% 2.38/1.32  ----------------------
% 2.38/1.32  Preprocessing        : 0.31
% 2.38/1.32  Parsing              : 0.18
% 2.38/1.32  CNF conversion       : 0.02
% 2.38/1.32  Main loop            : 0.29
% 2.38/1.32  Inferencing          : 0.12
% 2.38/1.32  Reduction            : 0.09
% 2.38/1.32  Demodulation         : 0.06
% 2.38/1.32  BG Simplification    : 0.02
% 2.38/1.32  Subsumption          : 0.05
% 2.38/1.32  Abstraction          : 0.01
% 2.38/1.32  MUC search           : 0.00
% 2.38/1.32  Cooper               : 0.00
% 2.38/1.32  Total                : 0.64
% 2.38/1.32  Index Insertion      : 0.00
% 2.38/1.32  Index Deletion       : 0.00
% 2.38/1.32  Index Matching       : 0.00
% 2.38/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
