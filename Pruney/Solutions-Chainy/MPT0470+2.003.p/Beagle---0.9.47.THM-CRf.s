%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:01 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 106 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 192 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_94,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_38,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_63,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_25] :
      ( v1_relat_1(A_25)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_51])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k5_relat_1(A_14,B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_2'(A_34,B_35),A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_34,B_35] :
      ( ~ v1_xboole_0(A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_160,plain,(
    ! [A_55,B_56] :
      ( k1_relat_1(k5_relat_1(A_55,B_56)) = k1_relat_1(A_55)
      | ~ r1_tarski(k2_relat_1(A_55),k1_relat_1(B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_169,plain,(
    ! [B_56] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_56)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_160])).

tff(c_275,plain,(
    ! [B_65] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_65)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_65))
      | ~ v1_relat_1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_36,c_169])).

tff(c_278,plain,(
    ! [B_65] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_65)) = k1_xboole_0
      | ~ v1_relat_1(B_65)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_86,c_275])).

tff(c_401,plain,(
    ! [B_67] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_67)) = k1_xboole_0
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_278])).

tff(c_26,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(k1_relat_1(A_16))
      | ~ v1_relat_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_410,plain,(
    ! [B_67] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_67))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_26])).

tff(c_486,plain,(
    ! [B_69] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_69))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_410])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_506,plain,(
    ! [B_70] :
      ( k5_relat_1(k1_xboole_0,B_70) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_486,c_14])).

tff(c_513,plain,(
    ! [B_15] :
      ( k5_relat_1(k1_xboole_0,B_15) = k1_xboole_0
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_506])).

tff(c_532,plain,(
    ! [B_74] :
      ( k5_relat_1(k1_xboole_0,B_74) = k1_xboole_0
      | ~ v1_relat_1(B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_513])).

tff(c_544,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_532])).

tff(c_552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_544])).

tff(c_553,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_643,plain,(
    ! [A_99,B_100] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_99,B_100)),k2_relat_1(B_100))
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_657,plain,(
    ! [A_99] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_99,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_643])).

tff(c_697,plain,(
    ! [A_103] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_103,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_657])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_619,plain,(
    ! [C_92,B_93,A_94] :
      ( r2_hidden(C_92,B_93)
      | ~ r2_hidden(C_92,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_626,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_1'(A_95),B_96)
      | ~ r1_tarski(A_95,B_96)
      | v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_4,c_619])).

tff(c_633,plain,(
    ! [B_96,A_95] :
      ( ~ v1_xboole_0(B_96)
      | ~ r1_tarski(A_95,B_96)
      | v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_626,c_2])).

tff(c_700,plain,(
    ! [A_103] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k2_relat_1(k5_relat_1(A_103,k1_xboole_0)))
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_697,c_633])).

tff(c_726,plain,(
    ! [A_107] :
      ( v1_xboole_0(k2_relat_1(k5_relat_1(A_107,k1_xboole_0)))
      | ~ v1_relat_1(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_700])).

tff(c_28,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(k2_relat_1(A_17))
      | ~ v1_relat_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_884,plain,(
    ! [A_117] :
      ( ~ v1_relat_1(k5_relat_1(A_117,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_117,k1_xboole_0))
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_726,c_28])).

tff(c_1139,plain,(
    ! [A_128] :
      ( k5_relat_1(A_128,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_128,k1_xboole_0))
      | ~ v1_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_884,c_14])).

tff(c_1146,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_24,c_1139])).

tff(c_1152,plain,(
    ! [A_129] :
      ( k5_relat_1(A_129,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1146])).

tff(c_1164,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_1152])).

tff(c_1172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_553,c_1164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.41  
% 3.00/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.41  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 3.00/1.41  
% 3.00/1.41  %Foreground sorts:
% 3.00/1.41  
% 3.00/1.41  
% 3.00/1.41  %Background operators:
% 3.00/1.41  
% 3.00/1.41  
% 3.00/1.41  %Foreground operators:
% 3.00/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.00/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.00/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.00/1.41  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.00/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.00/1.41  
% 3.00/1.43  tff(f_101, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.00/1.43  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.00/1.43  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.00/1.43  tff(f_59, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.00/1.43  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.00/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.00/1.43  tff(f_94, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.00/1.43  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.00/1.43  tff(f_67, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.00/1.43  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.00/1.43  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.00/1.43  tff(f_75, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.00/1.43  tff(c_38, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.00/1.43  tff(c_63, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 3.00/1.43  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.00/1.43  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.00/1.43  tff(c_51, plain, (![A_25]: (v1_relat_1(A_25) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.43  tff(c_55, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_51])).
% 3.00/1.43  tff(c_24, plain, (![A_14, B_15]: (v1_relat_1(k5_relat_1(A_14, B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.00/1.43  tff(c_82, plain, (![A_34, B_35]: (r2_hidden('#skF_2'(A_34, B_35), A_34) | r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.00/1.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.00/1.43  tff(c_86, plain, (![A_34, B_35]: (~v1_xboole_0(A_34) | r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_82, c_2])).
% 3.00/1.43  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.00/1.43  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.00/1.43  tff(c_160, plain, (![A_55, B_56]: (k1_relat_1(k5_relat_1(A_55, B_56))=k1_relat_1(A_55) | ~r1_tarski(k2_relat_1(A_55), k1_relat_1(B_56)) | ~v1_relat_1(B_56) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.00/1.43  tff(c_169, plain, (![B_56]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_56))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_56)) | ~v1_relat_1(B_56) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_160])).
% 3.00/1.43  tff(c_275, plain, (![B_65]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_65))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_relat_1(B_65)) | ~v1_relat_1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_36, c_169])).
% 3.00/1.43  tff(c_278, plain, (![B_65]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_65))=k1_xboole_0 | ~v1_relat_1(B_65) | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_86, c_275])).
% 3.00/1.43  tff(c_401, plain, (![B_67]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_67))=k1_xboole_0 | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_278])).
% 3.00/1.43  tff(c_26, plain, (![A_16]: (~v1_xboole_0(k1_relat_1(A_16)) | ~v1_relat_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.00/1.43  tff(c_410, plain, (![B_67]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_67)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_67)) | ~v1_relat_1(B_67))), inference(superposition, [status(thm), theory('equality')], [c_401, c_26])).
% 3.00/1.43  tff(c_486, plain, (![B_69]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_69)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_69)) | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_410])).
% 3.00/1.43  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.00/1.43  tff(c_506, plain, (![B_70]: (k5_relat_1(k1_xboole_0, B_70)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_70)) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_486, c_14])).
% 3.00/1.43  tff(c_513, plain, (![B_15]: (k5_relat_1(k1_xboole_0, B_15)=k1_xboole_0 | ~v1_relat_1(B_15) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_506])).
% 3.00/1.43  tff(c_532, plain, (![B_74]: (k5_relat_1(k1_xboole_0, B_74)=k1_xboole_0 | ~v1_relat_1(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_513])).
% 3.00/1.43  tff(c_544, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_532])).
% 3.00/1.43  tff(c_552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_544])).
% 3.00/1.43  tff(c_553, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 3.00/1.43  tff(c_643, plain, (![A_99, B_100]: (r1_tarski(k2_relat_1(k5_relat_1(A_99, B_100)), k2_relat_1(B_100)) | ~v1_relat_1(B_100) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.00/1.43  tff(c_657, plain, (![A_99]: (r1_tarski(k2_relat_1(k5_relat_1(A_99, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_99))), inference(superposition, [status(thm), theory('equality')], [c_34, c_643])).
% 3.00/1.43  tff(c_697, plain, (![A_103]: (r1_tarski(k2_relat_1(k5_relat_1(A_103, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_657])).
% 3.00/1.43  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.00/1.43  tff(c_619, plain, (![C_92, B_93, A_94]: (r2_hidden(C_92, B_93) | ~r2_hidden(C_92, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.00/1.43  tff(c_626, plain, (![A_95, B_96]: (r2_hidden('#skF_1'(A_95), B_96) | ~r1_tarski(A_95, B_96) | v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_4, c_619])).
% 3.00/1.43  tff(c_633, plain, (![B_96, A_95]: (~v1_xboole_0(B_96) | ~r1_tarski(A_95, B_96) | v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_626, c_2])).
% 3.00/1.43  tff(c_700, plain, (![A_103]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_relat_1(k5_relat_1(A_103, k1_xboole_0))) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_697, c_633])).
% 3.00/1.43  tff(c_726, plain, (![A_107]: (v1_xboole_0(k2_relat_1(k5_relat_1(A_107, k1_xboole_0))) | ~v1_relat_1(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_700])).
% 3.00/1.43  tff(c_28, plain, (![A_17]: (~v1_xboole_0(k2_relat_1(A_17)) | ~v1_relat_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.00/1.43  tff(c_884, plain, (![A_117]: (~v1_relat_1(k5_relat_1(A_117, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_117, k1_xboole_0)) | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_726, c_28])).
% 3.00/1.43  tff(c_1139, plain, (![A_128]: (k5_relat_1(A_128, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_128, k1_xboole_0)) | ~v1_relat_1(A_128))), inference(resolution, [status(thm)], [c_884, c_14])).
% 3.00/1.43  tff(c_1146, plain, (![A_14]: (k5_relat_1(A_14, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_24, c_1139])).
% 3.00/1.43  tff(c_1152, plain, (![A_129]: (k5_relat_1(A_129, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_1146])).
% 3.00/1.43  tff(c_1164, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_1152])).
% 3.00/1.43  tff(c_1172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_553, c_1164])).
% 3.00/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.43  
% 3.00/1.43  Inference rules
% 3.00/1.43  ----------------------
% 3.00/1.43  #Ref     : 0
% 3.00/1.43  #Sup     : 248
% 3.00/1.43  #Fact    : 0
% 3.00/1.43  #Define  : 0
% 3.00/1.43  #Split   : 4
% 3.00/1.43  #Chain   : 0
% 3.00/1.43  #Close   : 0
% 3.00/1.43  
% 3.00/1.43  Ordering : KBO
% 3.00/1.43  
% 3.00/1.43  Simplification rules
% 3.00/1.43  ----------------------
% 3.00/1.43  #Subsume      : 26
% 3.00/1.43  #Demod        : 226
% 3.00/1.43  #Tautology    : 122
% 3.00/1.43  #SimpNegUnit  : 2
% 3.00/1.43  #BackRed      : 4
% 3.00/1.43  
% 3.00/1.43  #Partial instantiations: 0
% 3.00/1.43  #Strategies tried      : 1
% 3.00/1.43  
% 3.00/1.43  Timing (in seconds)
% 3.00/1.43  ----------------------
% 3.00/1.43  Preprocessing        : 0.28
% 3.00/1.43  Parsing              : 0.16
% 3.00/1.43  CNF conversion       : 0.02
% 3.00/1.43  Main loop            : 0.38
% 3.00/1.43  Inferencing          : 0.15
% 3.00/1.43  Reduction            : 0.10
% 3.00/1.43  Demodulation         : 0.07
% 3.00/1.43  BG Simplification    : 0.02
% 3.00/1.43  Subsumption          : 0.08
% 3.00/1.43  Abstraction          : 0.02
% 3.00/1.43  MUC search           : 0.00
% 3.00/1.43  Cooper               : 0.00
% 3.00/1.43  Total                : 0.70
% 3.00/1.43  Index Insertion      : 0.00
% 3.00/1.43  Index Deletion       : 0.00
% 3.00/1.43  Index Matching       : 0.00
% 3.00/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
