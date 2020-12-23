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
% DateTime   : Thu Dec  3 10:02:17 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   63 (  80 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 117 expanded)
%              Number of equality atoms :   31 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_89,plain,(
    k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_72,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(k1_tarski(A_53),B_54)
      | r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [B_54,A_53] :
      ( r1_xboole_0(B_54,k1_tarski(A_53))
      | r2_hidden(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_118,plain,(
    ! [B_72,A_73] :
      ( k9_relat_1(B_72,A_73) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_72),A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_167,plain,(
    ! [B_87,A_88] :
      ( k9_relat_1(B_87,k1_tarski(A_88)) = k1_xboole_0
      | ~ v1_relat_1(B_87)
      | r2_hidden(A_88,k1_relat_1(B_87)) ) ),
    inference(resolution,[status(thm)],[c_75,c_118])).

tff(c_40,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_40])).

tff(c_170,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_167,c_90])).

tff(c_173,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_170])).

tff(c_30,plain,(
    ! [A_39,B_41] :
      ( k9_relat_1(A_39,k1_tarski(B_41)) = k11_relat_1(A_39,B_41)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_177,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_30])).

tff(c_184,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_177])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_184])).

tff(c_188,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_187,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_48,B_49] : k2_xboole_0(k1_tarski(A_48),B_49) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_69,plain,(
    ! [A_48] : k1_tarski(A_48) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_65])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_254,plain,(
    ! [A_112,B_113,C_114] :
      ( r1_tarski(k2_tarski(A_112,B_113),C_114)
      | ~ r2_hidden(B_113,C_114)
      | ~ r2_hidden(A_112,C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_272,plain,(
    ! [A_117,C_118] :
      ( r1_tarski(k1_tarski(A_117),C_118)
      | ~ r2_hidden(A_117,C_118)
      | ~ r2_hidden(A_117,C_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_254])).

tff(c_36,plain,(
    ! [B_45,A_44] :
      ( k9_relat_1(B_45,A_44) != k1_xboole_0
      | ~ r1_tarski(A_44,k1_relat_1(B_45))
      | k1_xboole_0 = A_44
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_276,plain,(
    ! [B_45,A_117] :
      ( k9_relat_1(B_45,k1_tarski(A_117)) != k1_xboole_0
      | k1_tarski(A_117) = k1_xboole_0
      | ~ v1_relat_1(B_45)
      | ~ r2_hidden(A_117,k1_relat_1(B_45)) ) ),
    inference(resolution,[status(thm)],[c_272,c_36])).

tff(c_285,plain,(
    ! [B_121,A_122] :
      ( k9_relat_1(B_121,k1_tarski(A_122)) != k1_xboole_0
      | ~ v1_relat_1(B_121)
      | ~ r2_hidden(A_122,k1_relat_1(B_121)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_276])).

tff(c_291,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_187,c_285])).

tff(c_295,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_291])).

tff(c_298,plain,
    ( k11_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_295])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_188,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:11:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.27  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.06/1.27  
% 2.06/1.27  %Foreground sorts:
% 2.06/1.27  
% 2.06/1.27  
% 2.06/1.27  %Background operators:
% 2.06/1.27  
% 2.06/1.27  
% 2.06/1.27  %Foreground operators:
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.27  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.06/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.06/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.27  
% 2.06/1.28  tff(f_88, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.06/1.28  tff(f_50, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.06/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.06/1.28  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.06/1.28  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.06/1.28  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.06/1.28  tff(f_59, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.06/1.28  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.06/1.28  tff(f_56, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.06/1.28  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 2.06/1.28  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.06/1.28  tff(c_46, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2')) | k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.06/1.28  tff(c_89, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 2.06/1.28  tff(c_72, plain, (![A_53, B_54]: (r1_xboole_0(k1_tarski(A_53), B_54) | r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.28  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.28  tff(c_75, plain, (![B_54, A_53]: (r1_xboole_0(B_54, k1_tarski(A_53)) | r2_hidden(A_53, B_54))), inference(resolution, [status(thm)], [c_72, c_2])).
% 2.06/1.28  tff(c_118, plain, (![B_72, A_73]: (k9_relat_1(B_72, A_73)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_72), A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.28  tff(c_167, plain, (![B_87, A_88]: (k9_relat_1(B_87, k1_tarski(A_88))=k1_xboole_0 | ~v1_relat_1(B_87) | r2_hidden(A_88, k1_relat_1(B_87)))), inference(resolution, [status(thm)], [c_75, c_118])).
% 2.06/1.28  tff(c_40, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.06/1.28  tff(c_90, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_89, c_40])).
% 2.06/1.28  tff(c_170, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_167, c_90])).
% 2.06/1.28  tff(c_173, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_170])).
% 2.06/1.28  tff(c_30, plain, (![A_39, B_41]: (k9_relat_1(A_39, k1_tarski(B_41))=k11_relat_1(A_39, B_41) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.28  tff(c_177, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_173, c_30])).
% 2.06/1.28  tff(c_184, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_177])).
% 2.06/1.28  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_184])).
% 2.06/1.28  tff(c_188, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 2.06/1.28  tff(c_187, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_46])).
% 2.06/1.28  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.28  tff(c_65, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.06/1.28  tff(c_69, plain, (![A_48]: (k1_tarski(A_48)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_65])).
% 2.06/1.28  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.28  tff(c_254, plain, (![A_112, B_113, C_114]: (r1_tarski(k2_tarski(A_112, B_113), C_114) | ~r2_hidden(B_113, C_114) | ~r2_hidden(A_112, C_114))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.28  tff(c_272, plain, (![A_117, C_118]: (r1_tarski(k1_tarski(A_117), C_118) | ~r2_hidden(A_117, C_118) | ~r2_hidden(A_117, C_118))), inference(superposition, [status(thm), theory('equality')], [c_6, c_254])).
% 2.06/1.28  tff(c_36, plain, (![B_45, A_44]: (k9_relat_1(B_45, A_44)!=k1_xboole_0 | ~r1_tarski(A_44, k1_relat_1(B_45)) | k1_xboole_0=A_44 | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.06/1.28  tff(c_276, plain, (![B_45, A_117]: (k9_relat_1(B_45, k1_tarski(A_117))!=k1_xboole_0 | k1_tarski(A_117)=k1_xboole_0 | ~v1_relat_1(B_45) | ~r2_hidden(A_117, k1_relat_1(B_45)))), inference(resolution, [status(thm)], [c_272, c_36])).
% 2.06/1.28  tff(c_285, plain, (![B_121, A_122]: (k9_relat_1(B_121, k1_tarski(A_122))!=k1_xboole_0 | ~v1_relat_1(B_121) | ~r2_hidden(A_122, k1_relat_1(B_121)))), inference(negUnitSimplification, [status(thm)], [c_69, c_276])).
% 2.06/1.28  tff(c_291, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_187, c_285])).
% 2.06/1.28  tff(c_295, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_291])).
% 2.06/1.28  tff(c_298, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_295])).
% 2.06/1.28  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_188, c_298])).
% 2.06/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.28  
% 2.06/1.28  Inference rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Ref     : 0
% 2.06/1.28  #Sup     : 55
% 2.06/1.28  #Fact    : 0
% 2.06/1.28  #Define  : 0
% 2.06/1.28  #Split   : 1
% 2.06/1.28  #Chain   : 0
% 2.06/1.28  #Close   : 0
% 2.06/1.28  
% 2.06/1.28  Ordering : KBO
% 2.06/1.28  
% 2.06/1.28  Simplification rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Subsume      : 5
% 2.06/1.28  #Demod        : 7
% 2.06/1.28  #Tautology    : 33
% 2.06/1.28  #SimpNegUnit  : 3
% 2.06/1.28  #BackRed      : 0
% 2.06/1.28  
% 2.06/1.28  #Partial instantiations: 0
% 2.06/1.28  #Strategies tried      : 1
% 2.06/1.28  
% 2.06/1.28  Timing (in seconds)
% 2.06/1.28  ----------------------
% 2.06/1.28  Preprocessing        : 0.31
% 2.06/1.28  Parsing              : 0.16
% 2.06/1.28  CNF conversion       : 0.02
% 2.06/1.28  Main loop            : 0.19
% 2.06/1.28  Inferencing          : 0.08
% 2.06/1.28  Reduction            : 0.05
% 2.06/1.28  Demodulation         : 0.03
% 2.06/1.28  BG Simplification    : 0.01
% 2.06/1.28  Subsumption          : 0.03
% 2.06/1.28  Abstraction          : 0.01
% 2.06/1.28  MUC search           : 0.00
% 2.06/1.29  Cooper               : 0.00
% 2.06/1.29  Total                : 0.53
% 2.06/1.29  Index Insertion      : 0.00
% 2.06/1.29  Index Deletion       : 0.00
% 2.06/1.29  Index Matching       : 0.00
% 2.06/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
