%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:52 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   71 (  96 expanded)
%              Number of leaves         :   37 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 169 expanded)
%              Number of equality atoms :   47 (  84 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_47,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_82,plain,(
    ! [A_47] :
      ( k1_relat_1(A_47) = k1_xboole_0
      | k2_relat_1(A_47) != k1_xboole_0
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_86,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_82])).

tff(c_87,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_1'(A_25,B_26),A_25)
      | k1_xboole_0 = A_25
      | k1_tarski(B_26) = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_142,plain,(
    ! [B_61,A_62] :
      ( k7_relat_1(B_61,A_62) = B_61
      | ~ r1_tarski(k1_relat_1(B_61),A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_148,plain,(
    ! [B_63] :
      ( k7_relat_1(B_63,k1_relat_1(B_63)) = B_63
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_8,c_142])).

tff(c_30,plain,(
    ! [B_32,A_31] :
      ( k2_relat_1(k7_relat_1(B_32,A_31)) = k9_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_161,plain,(
    ! [B_66] :
      ( k9_relat_1(B_66,k1_relat_1(B_66)) = k2_relat_1(B_66)
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_30])).

tff(c_50,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_121,plain,(
    ! [A_58,B_59] :
      ( k9_relat_1(A_58,k1_tarski(B_59)) = k11_relat_1(A_58,B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_130,plain,(
    ! [A_58] :
      ( k9_relat_1(A_58,k1_relat_1('#skF_3')) = k11_relat_1(A_58,'#skF_2')
      | ~ v1_relat_1(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_121])).

tff(c_168,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_130])).

tff(c_178,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_54,c_168])).

tff(c_32,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden(k4_tarski(A_33,B_34),C_35)
      | ~ r2_hidden(B_34,k11_relat_1(C_35,A_33))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_216,plain,(
    ! [C_85,A_86,B_87] :
      ( k1_funct_1(C_85,A_86) = B_87
      | ~ r2_hidden(k4_tarski(A_86,B_87),C_85)
      | ~ v1_funct_1(C_85)
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_293,plain,(
    ! [C_96,A_97,B_98] :
      ( k1_funct_1(C_96,A_97) = B_98
      | ~ v1_funct_1(C_96)
      | ~ r2_hidden(B_98,k11_relat_1(C_96,A_97))
      | ~ v1_relat_1(C_96) ) ),
    inference(resolution,[status(thm)],[c_32,c_216])).

tff(c_304,plain,(
    ! [B_98] :
      ( k1_funct_1('#skF_3','#skF_2') = B_98
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_98,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_293])).

tff(c_314,plain,(
    ! [B_99] :
      ( k1_funct_1('#skF_3','#skF_2') = B_99
      | ~ r2_hidden(B_99,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_304])).

tff(c_326,plain,(
    ! [B_26] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_26) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_26) ) ),
    inference(resolution,[status(thm)],[c_26,c_314])).

tff(c_332,plain,(
    ! [B_100] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_100) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_100) ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_326])).

tff(c_24,plain,(
    ! [A_25,B_26] :
      ( '#skF_1'(A_25,B_26) != B_26
      | k1_xboole_0 = A_25
      | k1_tarski(B_26) = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_340,plain,(
    ! [B_100] :
      ( k1_funct_1('#skF_3','#skF_2') != B_100
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_100)
      | k2_relat_1('#skF_3') = k1_tarski(B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_24])).

tff(c_348,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_340])).

tff(c_48,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_48])).

tff(c_352,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_22,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_tarski(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_22])).

tff(c_354,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_60])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:59:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.34  
% 2.35/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.35  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.35/1.35  
% 2.35/1.35  %Foreground sorts:
% 2.35/1.35  
% 2.35/1.35  
% 2.35/1.35  %Background operators:
% 2.35/1.35  
% 2.35/1.35  
% 2.35/1.35  %Foreground operators:
% 2.35/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.35/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.35/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.35/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.35/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.35/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.35  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.35/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.35/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.35/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.35/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.35  
% 2.35/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.35/1.36  tff(f_107, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.35/1.36  tff(f_82, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.35/1.36  tff(f_61, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.35/1.36  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.35/1.36  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.35/1.36  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.35/1.36  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.35/1.36  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.35/1.36  tff(f_98, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.35/1.36  tff(f_47, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.35/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.35/1.36  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.35/1.36  tff(c_82, plain, (![A_47]: (k1_relat_1(A_47)=k1_xboole_0 | k2_relat_1(A_47)!=k1_xboole_0 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.35/1.36  tff(c_86, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_82])).
% 2.35/1.36  tff(c_87, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_86])).
% 2.35/1.36  tff(c_26, plain, (![A_25, B_26]: (r2_hidden('#skF_1'(A_25, B_26), A_25) | k1_xboole_0=A_25 | k1_tarski(B_26)=A_25)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.35/1.36  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.35/1.36  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.35/1.36  tff(c_142, plain, (![B_61, A_62]: (k7_relat_1(B_61, A_62)=B_61 | ~r1_tarski(k1_relat_1(B_61), A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.35/1.36  tff(c_148, plain, (![B_63]: (k7_relat_1(B_63, k1_relat_1(B_63))=B_63 | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_8, c_142])).
% 2.35/1.36  tff(c_30, plain, (![B_32, A_31]: (k2_relat_1(k7_relat_1(B_32, A_31))=k9_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.35/1.36  tff(c_161, plain, (![B_66]: (k9_relat_1(B_66, k1_relat_1(B_66))=k2_relat_1(B_66) | ~v1_relat_1(B_66) | ~v1_relat_1(B_66))), inference(superposition, [status(thm), theory('equality')], [c_148, c_30])).
% 2.35/1.36  tff(c_50, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.35/1.36  tff(c_121, plain, (![A_58, B_59]: (k9_relat_1(A_58, k1_tarski(B_59))=k11_relat_1(A_58, B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.35/1.36  tff(c_130, plain, (![A_58]: (k9_relat_1(A_58, k1_relat_1('#skF_3'))=k11_relat_1(A_58, '#skF_2') | ~v1_relat_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_50, c_121])).
% 2.35/1.36  tff(c_168, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_161, c_130])).
% 2.35/1.36  tff(c_178, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_54, c_168])).
% 2.35/1.36  tff(c_32, plain, (![A_33, B_34, C_35]: (r2_hidden(k4_tarski(A_33, B_34), C_35) | ~r2_hidden(B_34, k11_relat_1(C_35, A_33)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.35/1.36  tff(c_216, plain, (![C_85, A_86, B_87]: (k1_funct_1(C_85, A_86)=B_87 | ~r2_hidden(k4_tarski(A_86, B_87), C_85) | ~v1_funct_1(C_85) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.35/1.36  tff(c_293, plain, (![C_96, A_97, B_98]: (k1_funct_1(C_96, A_97)=B_98 | ~v1_funct_1(C_96) | ~r2_hidden(B_98, k11_relat_1(C_96, A_97)) | ~v1_relat_1(C_96))), inference(resolution, [status(thm)], [c_32, c_216])).
% 2.35/1.36  tff(c_304, plain, (![B_98]: (k1_funct_1('#skF_3', '#skF_2')=B_98 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_98, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_293])).
% 2.35/1.36  tff(c_314, plain, (![B_99]: (k1_funct_1('#skF_3', '#skF_2')=B_99 | ~r2_hidden(B_99, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_304])).
% 2.35/1.36  tff(c_326, plain, (![B_26]: ('#skF_1'(k2_relat_1('#skF_3'), B_26)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_26))), inference(resolution, [status(thm)], [c_26, c_314])).
% 2.35/1.36  tff(c_332, plain, (![B_100]: ('#skF_1'(k2_relat_1('#skF_3'), B_100)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_100))), inference(negUnitSimplification, [status(thm)], [c_87, c_326])).
% 2.35/1.36  tff(c_24, plain, (![A_25, B_26]: ('#skF_1'(A_25, B_26)!=B_26 | k1_xboole_0=A_25 | k1_tarski(B_26)=A_25)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.35/1.36  tff(c_340, plain, (![B_100]: (k1_funct_1('#skF_3', '#skF_2')!=B_100 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_100) | k2_relat_1('#skF_3')=k1_tarski(B_100))), inference(superposition, [status(thm), theory('equality')], [c_332, c_24])).
% 2.35/1.36  tff(c_348, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_87, c_340])).
% 2.35/1.36  tff(c_48, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.35/1.36  tff(c_351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_348, c_48])).
% 2.35/1.36  tff(c_352, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_86])).
% 2.35/1.36  tff(c_22, plain, (![A_24]: (~v1_xboole_0(k1_tarski(A_24)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.35/1.36  tff(c_60, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_22])).
% 2.35/1.36  tff(c_354, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_352, c_60])).
% 2.35/1.36  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_354])).
% 2.35/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.36  
% 2.35/1.36  Inference rules
% 2.35/1.36  ----------------------
% 2.35/1.36  #Ref     : 0
% 2.35/1.36  #Sup     : 61
% 2.35/1.36  #Fact    : 0
% 2.35/1.36  #Define  : 0
% 2.35/1.36  #Split   : 2
% 2.35/1.36  #Chain   : 0
% 2.35/1.36  #Close   : 0
% 2.35/1.36  
% 2.35/1.36  Ordering : KBO
% 2.35/1.36  
% 2.35/1.36  Simplification rules
% 2.35/1.36  ----------------------
% 2.35/1.36  #Subsume      : 0
% 2.35/1.36  #Demod        : 18
% 2.35/1.36  #Tautology    : 34
% 2.35/1.36  #SimpNegUnit  : 5
% 2.35/1.36  #BackRed      : 4
% 2.35/1.36  
% 2.35/1.36  #Partial instantiations: 0
% 2.35/1.36  #Strategies tried      : 1
% 2.35/1.36  
% 2.35/1.36  Timing (in seconds)
% 2.35/1.36  ----------------------
% 2.60/1.37  Preprocessing        : 0.35
% 2.60/1.37  Parsing              : 0.19
% 2.60/1.37  CNF conversion       : 0.02
% 2.60/1.37  Main loop            : 0.22
% 2.60/1.37  Inferencing          : 0.08
% 2.60/1.37  Reduction            : 0.06
% 2.60/1.37  Demodulation         : 0.04
% 2.60/1.37  BG Simplification    : 0.02
% 2.60/1.37  Subsumption          : 0.03
% 2.60/1.37  Abstraction          : 0.01
% 2.60/1.37  MUC search           : 0.00
% 2.60/1.37  Cooper               : 0.00
% 2.60/1.37  Total                : 0.60
% 2.60/1.37  Index Insertion      : 0.00
% 2.60/1.37  Index Deletion       : 0.00
% 2.60/1.37  Index Matching       : 0.00
% 2.60/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
