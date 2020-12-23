%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:10 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 150 expanded)
%              Number of leaves         :   26 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  134 ( 426 expanded)
%              Number of equality atoms :   11 (  39 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(c_38,plain,(
    k1_funct_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') != k1_funct_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_65,plain,(
    ! [A_38,B_39] :
      ( k5_relat_1(k6_relat_1(A_38),B_39) = k7_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,(
    ! [B_39,A_38] :
      ( v1_relat_1(k7_relat_1(B_39,A_38))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_8])).

tff(c_77,plain,(
    ! [B_39,A_38] :
      ( v1_relat_1(k7_relat_1(B_39,A_38))
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_71])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    r2_hidden('#skF_2',k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k7_relat_1(B_10,A_9),B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_131,plain,(
    ! [A_62,C_63] :
      ( r2_hidden(k4_tarski(A_62,k1_funct_1(C_63,A_62)),C_63)
      | ~ r2_hidden(A_62,k1_relat_1(C_63))
      | ~ v1_funct_1(C_63)
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_161,plain,(
    ! [A_69,C_70,B_71] :
      ( r2_hidden(k4_tarski(A_69,k1_funct_1(C_70,A_69)),B_71)
      | ~ r1_tarski(C_70,B_71)
      | ~ r2_hidden(A_69,k1_relat_1(C_70))
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_131,c_2])).

tff(c_36,plain,(
    ! [A_21,C_23,B_22] :
      ( r2_hidden(A_21,k1_relat_1(C_23))
      | ~ r2_hidden(k4_tarski(A_21,B_22),C_23)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_224,plain,(
    ! [A_91,B_92,C_93] :
      ( r2_hidden(A_91,k1_relat_1(B_92))
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ r1_tarski(C_93,B_92)
      | ~ r2_hidden(A_91,k1_relat_1(C_93))
      | ~ v1_funct_1(C_93)
      | ~ v1_relat_1(C_93) ) ),
    inference(resolution,[status(thm)],[c_161,c_36])).

tff(c_312,plain,(
    ! [A_117,B_118,A_119] :
      ( r2_hidden(A_117,k1_relat_1(B_118))
      | ~ v1_funct_1(B_118)
      | ~ r2_hidden(A_117,k1_relat_1(k7_relat_1(B_118,A_119)))
      | ~ v1_funct_1(k7_relat_1(B_118,A_119))
      | ~ v1_relat_1(k7_relat_1(B_118,A_119))
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_12,c_224])).

tff(c_343,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_312])).

tff(c_353,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_343])).

tff(c_354,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_357,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_354])).

tff(c_361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_357])).

tff(c_363,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_30,plain,(
    ! [A_20] : v1_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_87,plain,(
    ! [A_43,B_44] :
      ( v1_funct_1(k5_relat_1(A_43,B_44))
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_90,plain,(
    ! [B_12,A_11] :
      ( v1_funct_1(k7_relat_1(B_12,A_11))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_92,plain,(
    ! [B_12,A_11] :
      ( v1_funct_1(k7_relat_1(B_12,A_11))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_90])).

tff(c_362,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3'))
    | r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_364,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_362])).

tff(c_367,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_364])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_367])).

tff(c_373,plain,(
    v1_funct_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_362])).

tff(c_34,plain,(
    ! [C_23,A_21,B_22] :
      ( k1_funct_1(C_23,A_21) = B_22
      | ~ r2_hidden(k4_tarski(A_21,B_22),C_23)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_288,plain,(
    ! [C_109,A_110,B_111] :
      ( k1_funct_1(C_109,A_110) = k1_funct_1(B_111,A_110)
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111)
      | ~ r1_tarski(C_109,B_111)
      | ~ r2_hidden(A_110,k1_relat_1(C_109))
      | ~ v1_funct_1(C_109)
      | ~ v1_relat_1(C_109) ) ),
    inference(resolution,[status(thm)],[c_161,c_34])).

tff(c_1201,plain,(
    ! [B_198,A_199,A_200] :
      ( k1_funct_1(k7_relat_1(B_198,A_199),A_200) = k1_funct_1(B_198,A_200)
      | ~ v1_funct_1(B_198)
      | ~ r2_hidden(A_200,k1_relat_1(k7_relat_1(B_198,A_199)))
      | ~ v1_funct_1(k7_relat_1(B_198,A_199))
      | ~ v1_relat_1(k7_relat_1(B_198,A_199))
      | ~ v1_relat_1(B_198) ) ),
    inference(resolution,[status(thm)],[c_12,c_288])).

tff(c_1244,plain,
    ( k1_funct_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') = k1_funct_1('#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1201])).

tff(c_1257,plain,(
    k1_funct_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') = k1_funct_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_363,c_373,c_42,c_1244])).

tff(c_1259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.62  
% 3.50/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.62  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.50/1.62  
% 3.50/1.62  %Foreground sorts:
% 3.50/1.62  
% 3.50/1.62  
% 3.50/1.62  %Background operators:
% 3.50/1.62  
% 3.50/1.62  
% 3.50/1.62  %Foreground operators:
% 3.50/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.50/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.50/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.50/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.50/1.62  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.50/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.50/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.50/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.62  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.50/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.88/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.88/1.62  
% 3.88/1.63  tff(f_101, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 3.88/1.63  tff(f_82, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.88/1.63  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.88/1.63  tff(f_38, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.88/1.63  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.88/1.63  tff(f_92, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.88/1.63  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.88/1.63  tff(f_78, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 3.88/1.63  tff(c_38, plain, (k1_funct_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')!=k1_funct_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.88/1.63  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.88/1.63  tff(c_28, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.88/1.63  tff(c_65, plain, (![A_38, B_39]: (k5_relat_1(k6_relat_1(A_38), B_39)=k7_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.88/1.63  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.88/1.63  tff(c_71, plain, (![B_39, A_38]: (v1_relat_1(k7_relat_1(B_39, A_38)) | ~v1_relat_1(B_39) | ~v1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(B_39))), inference(superposition, [status(thm), theory('equality')], [c_65, c_8])).
% 3.88/1.63  tff(c_77, plain, (![B_39, A_38]: (v1_relat_1(k7_relat_1(B_39, A_38)) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_71])).
% 3.88/1.63  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.88/1.63  tff(c_40, plain, (r2_hidden('#skF_2', k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.88/1.63  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k7_relat_1(B_10, A_9), B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.88/1.63  tff(c_131, plain, (![A_62, C_63]: (r2_hidden(k4_tarski(A_62, k1_funct_1(C_63, A_62)), C_63) | ~r2_hidden(A_62, k1_relat_1(C_63)) | ~v1_funct_1(C_63) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.88/1.63  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.63  tff(c_161, plain, (![A_69, C_70, B_71]: (r2_hidden(k4_tarski(A_69, k1_funct_1(C_70, A_69)), B_71) | ~r1_tarski(C_70, B_71) | ~r2_hidden(A_69, k1_relat_1(C_70)) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(resolution, [status(thm)], [c_131, c_2])).
% 3.88/1.63  tff(c_36, plain, (![A_21, C_23, B_22]: (r2_hidden(A_21, k1_relat_1(C_23)) | ~r2_hidden(k4_tarski(A_21, B_22), C_23) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.88/1.63  tff(c_224, plain, (![A_91, B_92, C_93]: (r2_hidden(A_91, k1_relat_1(B_92)) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~r1_tarski(C_93, B_92) | ~r2_hidden(A_91, k1_relat_1(C_93)) | ~v1_funct_1(C_93) | ~v1_relat_1(C_93))), inference(resolution, [status(thm)], [c_161, c_36])).
% 3.88/1.63  tff(c_312, plain, (![A_117, B_118, A_119]: (r2_hidden(A_117, k1_relat_1(B_118)) | ~v1_funct_1(B_118) | ~r2_hidden(A_117, k1_relat_1(k7_relat_1(B_118, A_119))) | ~v1_funct_1(k7_relat_1(B_118, A_119)) | ~v1_relat_1(k7_relat_1(B_118, A_119)) | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_12, c_224])).
% 3.88/1.63  tff(c_343, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_funct_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_312])).
% 3.88/1.63  tff(c_353, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_343])).
% 3.88/1.63  tff(c_354, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_353])).
% 3.88/1.63  tff(c_357, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_77, c_354])).
% 3.88/1.63  tff(c_361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_357])).
% 3.88/1.63  tff(c_363, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_353])).
% 3.88/1.63  tff(c_30, plain, (![A_20]: (v1_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.88/1.63  tff(c_14, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.88/1.63  tff(c_87, plain, (![A_43, B_44]: (v1_funct_1(k5_relat_1(A_43, B_44)) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.88/1.63  tff(c_90, plain, (![B_12, A_11]: (v1_funct_1(k7_relat_1(B_12, A_11)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(B_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_87])).
% 3.88/1.63  tff(c_92, plain, (![B_12, A_11]: (v1_funct_1(k7_relat_1(B_12, A_11)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_90])).
% 3.88/1.63  tff(c_362, plain, (~v1_funct_1(k7_relat_1('#skF_4', '#skF_3')) | r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_353])).
% 3.88/1.63  tff(c_364, plain, (~v1_funct_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_362])).
% 3.88/1.63  tff(c_367, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_364])).
% 3.88/1.63  tff(c_371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_367])).
% 3.88/1.63  tff(c_373, plain, (v1_funct_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_362])).
% 3.88/1.63  tff(c_34, plain, (![C_23, A_21, B_22]: (k1_funct_1(C_23, A_21)=B_22 | ~r2_hidden(k4_tarski(A_21, B_22), C_23) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.88/1.63  tff(c_288, plain, (![C_109, A_110, B_111]: (k1_funct_1(C_109, A_110)=k1_funct_1(B_111, A_110) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111) | ~r1_tarski(C_109, B_111) | ~r2_hidden(A_110, k1_relat_1(C_109)) | ~v1_funct_1(C_109) | ~v1_relat_1(C_109))), inference(resolution, [status(thm)], [c_161, c_34])).
% 3.88/1.63  tff(c_1201, plain, (![B_198, A_199, A_200]: (k1_funct_1(k7_relat_1(B_198, A_199), A_200)=k1_funct_1(B_198, A_200) | ~v1_funct_1(B_198) | ~r2_hidden(A_200, k1_relat_1(k7_relat_1(B_198, A_199))) | ~v1_funct_1(k7_relat_1(B_198, A_199)) | ~v1_relat_1(k7_relat_1(B_198, A_199)) | ~v1_relat_1(B_198))), inference(resolution, [status(thm)], [c_12, c_288])).
% 3.88/1.63  tff(c_1244, plain, (k1_funct_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')=k1_funct_1('#skF_4', '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_funct_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_1201])).
% 3.88/1.63  tff(c_1257, plain, (k1_funct_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')=k1_funct_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_363, c_373, c_42, c_1244])).
% 3.88/1.63  tff(c_1259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1257])).
% 3.88/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.63  
% 3.88/1.63  Inference rules
% 3.88/1.63  ----------------------
% 3.88/1.63  #Ref     : 0
% 3.88/1.63  #Sup     : 265
% 3.88/1.63  #Fact    : 0
% 3.88/1.63  #Define  : 0
% 3.88/1.63  #Split   : 5
% 3.88/1.63  #Chain   : 0
% 3.88/1.63  #Close   : 0
% 3.88/1.63  
% 3.88/1.63  Ordering : KBO
% 3.88/1.63  
% 3.88/1.63  Simplification rules
% 3.88/1.63  ----------------------
% 3.88/1.63  #Subsume      : 45
% 3.88/1.63  #Demod        : 64
% 3.88/1.63  #Tautology    : 85
% 3.88/1.63  #SimpNegUnit  : 1
% 3.88/1.63  #BackRed      : 0
% 3.88/1.63  
% 3.88/1.63  #Partial instantiations: 0
% 3.88/1.63  #Strategies tried      : 1
% 3.88/1.63  
% 3.88/1.63  Timing (in seconds)
% 3.88/1.63  ----------------------
% 3.88/1.64  Preprocessing        : 0.30
% 3.88/1.64  Parsing              : 0.17
% 3.88/1.64  CNF conversion       : 0.02
% 3.88/1.64  Main loop            : 0.57
% 3.88/1.64  Inferencing          : 0.20
% 3.88/1.64  Reduction            : 0.15
% 3.88/1.64  Demodulation         : 0.11
% 3.88/1.64  BG Simplification    : 0.03
% 3.88/1.64  Subsumption          : 0.15
% 3.88/1.64  Abstraction          : 0.03
% 3.88/1.64  MUC search           : 0.00
% 3.88/1.64  Cooper               : 0.00
% 3.88/1.64  Total                : 0.90
% 3.88/1.64  Index Insertion      : 0.00
% 3.88/1.64  Index Deletion       : 0.00
% 3.88/1.64  Index Matching       : 0.00
% 3.88/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
