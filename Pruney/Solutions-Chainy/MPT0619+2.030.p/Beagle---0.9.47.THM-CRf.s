%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:55 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 126 expanded)
%              Number of leaves         :   35 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 222 expanded)
%              Number of equality atoms :   40 ( 101 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_157,plain,(
    ! [A_74,B_75] :
      ( k9_relat_1(A_74,k1_tarski(B_75)) = k11_relat_1(A_74,B_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_169,plain,(
    ! [A_76] :
      ( k9_relat_1(A_76,k1_relat_1('#skF_3')) = k11_relat_1(A_76,'#skF_2')
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_157])).

tff(c_30,plain,(
    ! [A_40] :
      ( k9_relat_1(A_40,k1_relat_1(A_40)) = k2_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_176,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_30])).

tff(c_186,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_176])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_50,B_51] : r1_tarski(k1_tarski(A_50),k2_tarski(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,(
    ! [A_1] : r1_tarski(k1_tarski(A_1),k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_98,plain,(
    ! [B_56,C_57,A_58] :
      ( r2_hidden(B_56,C_57)
      | ~ r1_tarski(k2_tarski(A_58,B_56),C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    ! [A_59,C_60] :
      ( r2_hidden(A_59,C_60)
      | ~ r1_tarski(k1_tarski(A_59),C_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_114,plain,(
    ! [A_61] : r2_hidden(A_61,k1_tarski(A_61)) ),
    inference(resolution,[status(thm)],[c_69,c_102])).

tff(c_117,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_114])).

tff(c_197,plain,(
    ! [B_81,A_82] :
      ( k11_relat_1(B_81,A_82) != k1_xboole_0
      | ~ r2_hidden(A_82,k1_relat_1(B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_207,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_197])).

tff(c_212,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_186,c_207])).

tff(c_26,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_1'(A_34,B_35),A_34)
      | k1_xboole_0 = A_34
      | k1_tarski(B_35) = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    ! [A_41,B_42,C_43] :
      ( r2_hidden(k4_tarski(A_41,B_42),C_43)
      | ~ r2_hidden(B_42,k11_relat_1(C_43,A_41))
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_293,plain,(
    ! [C_102,A_103,B_104] :
      ( k1_funct_1(C_102,A_103) = B_104
      | ~ r2_hidden(k4_tarski(A_103,B_104),C_102)
      | ~ v1_funct_1(C_102)
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_358,plain,(
    ! [C_115,A_116,B_117] :
      ( k1_funct_1(C_115,A_116) = B_117
      | ~ v1_funct_1(C_115)
      | ~ r2_hidden(B_117,k11_relat_1(C_115,A_116))
      | ~ v1_relat_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_32,c_293])).

tff(c_373,plain,(
    ! [B_117] :
      ( k1_funct_1('#skF_3','#skF_2') = B_117
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_117,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_358])).

tff(c_379,plain,(
    ! [B_118] :
      ( k1_funct_1('#skF_3','#skF_2') = B_118
      | ~ r2_hidden(B_118,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_373])).

tff(c_391,plain,(
    ! [B_35] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_35) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_35) ) ),
    inference(resolution,[status(thm)],[c_26,c_379])).

tff(c_397,plain,(
    ! [B_119] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_119) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_391])).

tff(c_24,plain,(
    ! [A_34,B_35] :
      ( '#skF_1'(A_34,B_35) != B_35
      | k1_xboole_0 = A_34
      | k1_tarski(B_35) = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_405,plain,(
    ! [B_119] :
      ( k1_funct_1('#skF_3','#skF_2') != B_119
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_119)
      | k2_relat_1('#skF_3') = k1_tarski(B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_24])).

tff(c_413,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_405])).

tff(c_46,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.33  
% 2.30/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.34  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.34  
% 2.30/1.34  %Foreground sorts:
% 2.30/1.34  
% 2.30/1.34  
% 2.30/1.34  %Background operators:
% 2.30/1.34  
% 2.30/1.34  
% 2.30/1.34  %Foreground operators:
% 2.30/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.30/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.30/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.30/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.34  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.30/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.30/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.30/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.30/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.34  
% 2.57/1.35  tff(f_102, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.57/1.35  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.57/1.35  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.57/1.35  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.57/1.35  tff(f_41, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.57/1.35  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.57/1.35  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.57/1.35  tff(f_61, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.57/1.35  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.57/1.35  tff(f_93, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.57/1.35  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.57/1.35  tff(c_48, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.57/1.35  tff(c_157, plain, (![A_74, B_75]: (k9_relat_1(A_74, k1_tarski(B_75))=k11_relat_1(A_74, B_75) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.57/1.35  tff(c_169, plain, (![A_76]: (k9_relat_1(A_76, k1_relat_1('#skF_3'))=k11_relat_1(A_76, '#skF_2') | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_48, c_157])).
% 2.57/1.35  tff(c_30, plain, (![A_40]: (k9_relat_1(A_40, k1_relat_1(A_40))=k2_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.57/1.35  tff(c_176, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_169, c_30])).
% 2.57/1.35  tff(c_186, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_176])).
% 2.57/1.35  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.57/1.35  tff(c_66, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), k2_tarski(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.57/1.35  tff(c_69, plain, (![A_1]: (r1_tarski(k1_tarski(A_1), k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_66])).
% 2.57/1.35  tff(c_98, plain, (![B_56, C_57, A_58]: (r2_hidden(B_56, C_57) | ~r1_tarski(k2_tarski(A_58, B_56), C_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.57/1.35  tff(c_102, plain, (![A_59, C_60]: (r2_hidden(A_59, C_60) | ~r1_tarski(k1_tarski(A_59), C_60))), inference(superposition, [status(thm), theory('equality')], [c_2, c_98])).
% 2.57/1.35  tff(c_114, plain, (![A_61]: (r2_hidden(A_61, k1_tarski(A_61)))), inference(resolution, [status(thm)], [c_69, c_102])).
% 2.57/1.35  tff(c_117, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_114])).
% 2.57/1.35  tff(c_197, plain, (![B_81, A_82]: (k11_relat_1(B_81, A_82)!=k1_xboole_0 | ~r2_hidden(A_82, k1_relat_1(B_81)) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.57/1.35  tff(c_207, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_117, c_197])).
% 2.57/1.35  tff(c_212, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_186, c_207])).
% 2.57/1.35  tff(c_26, plain, (![A_34, B_35]: (r2_hidden('#skF_1'(A_34, B_35), A_34) | k1_xboole_0=A_34 | k1_tarski(B_35)=A_34)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.57/1.35  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.57/1.35  tff(c_32, plain, (![A_41, B_42, C_43]: (r2_hidden(k4_tarski(A_41, B_42), C_43) | ~r2_hidden(B_42, k11_relat_1(C_43, A_41)) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.57/1.35  tff(c_293, plain, (![C_102, A_103, B_104]: (k1_funct_1(C_102, A_103)=B_104 | ~r2_hidden(k4_tarski(A_103, B_104), C_102) | ~v1_funct_1(C_102) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.57/1.35  tff(c_358, plain, (![C_115, A_116, B_117]: (k1_funct_1(C_115, A_116)=B_117 | ~v1_funct_1(C_115) | ~r2_hidden(B_117, k11_relat_1(C_115, A_116)) | ~v1_relat_1(C_115))), inference(resolution, [status(thm)], [c_32, c_293])).
% 2.57/1.35  tff(c_373, plain, (![B_117]: (k1_funct_1('#skF_3', '#skF_2')=B_117 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_117, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_358])).
% 2.57/1.35  tff(c_379, plain, (![B_118]: (k1_funct_1('#skF_3', '#skF_2')=B_118 | ~r2_hidden(B_118, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_373])).
% 2.57/1.35  tff(c_391, plain, (![B_35]: ('#skF_1'(k2_relat_1('#skF_3'), B_35)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_35))), inference(resolution, [status(thm)], [c_26, c_379])).
% 2.57/1.35  tff(c_397, plain, (![B_119]: ('#skF_1'(k2_relat_1('#skF_3'), B_119)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_119))), inference(negUnitSimplification, [status(thm)], [c_212, c_391])).
% 2.57/1.35  tff(c_24, plain, (![A_34, B_35]: ('#skF_1'(A_34, B_35)!=B_35 | k1_xboole_0=A_34 | k1_tarski(B_35)=A_34)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.57/1.35  tff(c_405, plain, (![B_119]: (k1_funct_1('#skF_3', '#skF_2')!=B_119 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_119) | k2_relat_1('#skF_3')=k1_tarski(B_119))), inference(superposition, [status(thm), theory('equality')], [c_397, c_24])).
% 2.57/1.35  tff(c_413, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_212, c_405])).
% 2.57/1.35  tff(c_46, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.57/1.35  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_413, c_46])).
% 2.57/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.35  
% 2.57/1.35  Inference rules
% 2.57/1.35  ----------------------
% 2.57/1.35  #Ref     : 0
% 2.57/1.35  #Sup     : 78
% 2.57/1.35  #Fact    : 0
% 2.57/1.35  #Define  : 0
% 2.57/1.35  #Split   : 0
% 2.57/1.35  #Chain   : 0
% 2.57/1.35  #Close   : 0
% 2.57/1.35  
% 2.57/1.35  Ordering : KBO
% 2.57/1.35  
% 2.57/1.35  Simplification rules
% 2.57/1.35  ----------------------
% 2.57/1.35  #Subsume      : 2
% 2.57/1.35  #Demod        : 21
% 2.57/1.35  #Tautology    : 37
% 2.57/1.35  #SimpNegUnit  : 3
% 2.57/1.35  #BackRed      : 1
% 2.57/1.35  
% 2.57/1.35  #Partial instantiations: 0
% 2.57/1.35  #Strategies tried      : 1
% 2.57/1.35  
% 2.57/1.35  Timing (in seconds)
% 2.57/1.35  ----------------------
% 2.57/1.35  Preprocessing        : 0.34
% 2.57/1.35  Parsing              : 0.18
% 2.57/1.35  CNF conversion       : 0.02
% 2.57/1.35  Main loop            : 0.25
% 2.57/1.35  Inferencing          : 0.09
% 2.57/1.35  Reduction            : 0.08
% 2.57/1.35  Demodulation         : 0.06
% 2.57/1.35  BG Simplification    : 0.02
% 2.57/1.35  Subsumption          : 0.04
% 2.57/1.35  Abstraction          : 0.01
% 2.57/1.35  MUC search           : 0.00
% 2.57/1.35  Cooper               : 0.00
% 2.57/1.35  Total                : 0.62
% 2.57/1.35  Index Insertion      : 0.00
% 2.57/1.35  Index Deletion       : 0.00
% 2.57/1.35  Index Matching       : 0.00
% 2.57/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
