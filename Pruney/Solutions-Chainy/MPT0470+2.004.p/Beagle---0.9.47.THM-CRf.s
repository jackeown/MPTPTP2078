%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:01 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 113 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 206 expanded)
%              Number of equality atoms :   28 (  39 expanded)
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

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_96,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_38,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_62,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_26] :
      ( v1_relat_1(A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_51])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k5_relat_1(A_15,B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_160,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_56,B_57)),k1_relat_1(A_56))
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_171,plain,(
    ! [B_57] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_57)),k1_xboole_0)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_160])).

tff(c_244,plain,(
    ! [B_62] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_62)),k1_xboole_0)
      | ~ v1_relat_1(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_171])).

tff(c_92,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_2'(A_37,B_38),A_37)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_39,B_40] :
      ( ~ v1_xboole_0(A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_100,plain,(
    ! [B_40,A_39] :
      ( B_40 = A_39
      | ~ r1_tarski(B_40,A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_97,c_14])).

tff(c_250,plain,(
    ! [B_62] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_62)) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_244,c_100])).

tff(c_276,plain,(
    ! [B_64] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_64)) = k1_xboole_0
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_250])).

tff(c_26,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(k1_relat_1(A_17))
      | ~ v1_relat_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_294,plain,(
    ! [B_64] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_64))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_26])).

tff(c_498,plain,(
    ! [B_85] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_85))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_85))
      | ~ v1_relat_1(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_294])).

tff(c_63,plain,(
    ! [B_30,A_31] :
      ( ~ v1_xboole_0(B_30)
      | B_30 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ! [A_31] :
      ( k1_xboole_0 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_12,c_63])).

tff(c_534,plain,(
    ! [B_87] :
      ( k5_relat_1(k1_xboole_0,B_87) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_498,c_66])).

tff(c_538,plain,(
    ! [B_16] :
      ( k5_relat_1(k1_xboole_0,B_16) = k1_xboole_0
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_534])).

tff(c_542,plain,(
    ! [B_88] :
      ( k5_relat_1(k1_xboole_0,B_88) = k1_xboole_0
      | ~ v1_relat_1(B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_538])).

tff(c_557,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_542])).

tff(c_565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_557])).

tff(c_566,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_657,plain,(
    ! [A_113,B_114] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_113,B_114)),k2_relat_1(B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_671,plain,(
    ! [A_113] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_113,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_657])).

tff(c_696,plain,(
    ! [A_115] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_115,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_671])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_623,plain,(
    ! [C_104,B_105,A_106] :
      ( r2_hidden(C_104,B_105)
      | ~ r2_hidden(C_104,A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_640,plain,(
    ! [A_109,B_110] :
      ( r2_hidden('#skF_1'(A_109),B_110)
      | ~ r1_tarski(A_109,B_110)
      | v1_xboole_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_4,c_623])).

tff(c_647,plain,(
    ! [B_110,A_109] :
      ( ~ v1_xboole_0(B_110)
      | ~ r1_tarski(A_109,B_110)
      | v1_xboole_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_640,c_2])).

tff(c_699,plain,(
    ! [A_115] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k2_relat_1(k5_relat_1(A_115,k1_xboole_0)))
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_696,c_647])).

tff(c_734,plain,(
    ! [A_118] :
      ( v1_xboole_0(k2_relat_1(k5_relat_1(A_118,k1_xboole_0)))
      | ~ v1_relat_1(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_699])).

tff(c_28,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k2_relat_1(A_18))
      | ~ v1_relat_1(A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1077,plain,(
    ! [A_144] :
      ( ~ v1_relat_1(k5_relat_1(A_144,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_144,k1_xboole_0))
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_734,c_28])).

tff(c_572,plain,(
    ! [B_89,A_90] :
      ( ~ v1_xboole_0(B_89)
      | B_89 = A_90
      | ~ v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_575,plain,(
    ! [A_90] :
      ( k1_xboole_0 = A_90
      | ~ v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_12,c_572])).

tff(c_1095,plain,(
    ! [A_145] :
      ( k5_relat_1(A_145,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_145,k1_xboole_0))
      | ~ v1_relat_1(A_145) ) ),
    inference(resolution,[status(thm)],[c_1077,c_575])).

tff(c_1099,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_24,c_1095])).

tff(c_1103,plain,(
    ! [A_146] :
      ( k5_relat_1(A_146,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1099])).

tff(c_1118,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_1103])).

tff(c_1126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_1118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:41:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.54  
% 2.90/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.55  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.90/1.55  
% 2.90/1.55  %Foreground sorts:
% 2.90/1.55  
% 2.90/1.55  
% 2.90/1.55  %Background operators:
% 2.90/1.55  
% 2.90/1.55  
% 2.90/1.55  %Foreground operators:
% 2.90/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.90/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.55  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.90/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.90/1.55  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.90/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.55  
% 3.26/1.56  tff(f_103, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.26/1.56  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.26/1.56  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.26/1.56  tff(f_63, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.26/1.56  tff(f_96, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.26/1.56  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.26/1.56  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.26/1.56  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.26/1.56  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.26/1.56  tff(f_71, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.26/1.56  tff(f_53, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.26/1.56  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.26/1.56  tff(f_79, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.26/1.56  tff(c_38, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.26/1.56  tff(c_62, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 3.26/1.56  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.26/1.56  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.56  tff(c_51, plain, (![A_26]: (v1_relat_1(A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.26/1.56  tff(c_55, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_51])).
% 3.26/1.56  tff(c_24, plain, (![A_15, B_16]: (v1_relat_1(k5_relat_1(A_15, B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.26/1.56  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.26/1.56  tff(c_160, plain, (![A_56, B_57]: (r1_tarski(k1_relat_1(k5_relat_1(A_56, B_57)), k1_relat_1(A_56)) | ~v1_relat_1(B_57) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.26/1.56  tff(c_171, plain, (![B_57]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_57)), k1_xboole_0) | ~v1_relat_1(B_57) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_160])).
% 3.26/1.56  tff(c_244, plain, (![B_62]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_62)), k1_xboole_0) | ~v1_relat_1(B_62))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_171])).
% 3.26/1.56  tff(c_92, plain, (![A_37, B_38]: (r2_hidden('#skF_2'(A_37, B_38), A_37) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.26/1.56  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.56  tff(c_97, plain, (![A_39, B_40]: (~v1_xboole_0(A_39) | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_92, c_2])).
% 3.26/1.56  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.56  tff(c_100, plain, (![B_40, A_39]: (B_40=A_39 | ~r1_tarski(B_40, A_39) | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_97, c_14])).
% 3.26/1.56  tff(c_250, plain, (![B_62]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_62))=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_244, c_100])).
% 3.26/1.56  tff(c_276, plain, (![B_64]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_64))=k1_xboole_0 | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_250])).
% 3.26/1.56  tff(c_26, plain, (![A_17]: (~v1_xboole_0(k1_relat_1(A_17)) | ~v1_relat_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.26/1.56  tff(c_294, plain, (![B_64]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_64)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_64)) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_276, c_26])).
% 3.26/1.56  tff(c_498, plain, (![B_85]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_85)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_85)) | ~v1_relat_1(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_294])).
% 3.26/1.56  tff(c_63, plain, (![B_30, A_31]: (~v1_xboole_0(B_30) | B_30=A_31 | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.26/1.56  tff(c_66, plain, (![A_31]: (k1_xboole_0=A_31 | ~v1_xboole_0(A_31))), inference(resolution, [status(thm)], [c_12, c_63])).
% 3.26/1.56  tff(c_534, plain, (![B_87]: (k5_relat_1(k1_xboole_0, B_87)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_87)) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_498, c_66])).
% 3.26/1.56  tff(c_538, plain, (![B_16]: (k5_relat_1(k1_xboole_0, B_16)=k1_xboole_0 | ~v1_relat_1(B_16) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_534])).
% 3.26/1.56  tff(c_542, plain, (![B_88]: (k5_relat_1(k1_xboole_0, B_88)=k1_xboole_0 | ~v1_relat_1(B_88))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_538])).
% 3.26/1.56  tff(c_557, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_542])).
% 3.26/1.56  tff(c_565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_557])).
% 3.26/1.56  tff(c_566, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 3.26/1.56  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.26/1.56  tff(c_657, plain, (![A_113, B_114]: (r1_tarski(k2_relat_1(k5_relat_1(A_113, B_114)), k2_relat_1(B_114)) | ~v1_relat_1(B_114) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.56  tff(c_671, plain, (![A_113]: (r1_tarski(k2_relat_1(k5_relat_1(A_113, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_113))), inference(superposition, [status(thm), theory('equality')], [c_34, c_657])).
% 3.26/1.56  tff(c_696, plain, (![A_115]: (r1_tarski(k2_relat_1(k5_relat_1(A_115, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_671])).
% 3.26/1.56  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.56  tff(c_623, plain, (![C_104, B_105, A_106]: (r2_hidden(C_104, B_105) | ~r2_hidden(C_104, A_106) | ~r1_tarski(A_106, B_105))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.26/1.56  tff(c_640, plain, (![A_109, B_110]: (r2_hidden('#skF_1'(A_109), B_110) | ~r1_tarski(A_109, B_110) | v1_xboole_0(A_109))), inference(resolution, [status(thm)], [c_4, c_623])).
% 3.26/1.56  tff(c_647, plain, (![B_110, A_109]: (~v1_xboole_0(B_110) | ~r1_tarski(A_109, B_110) | v1_xboole_0(A_109))), inference(resolution, [status(thm)], [c_640, c_2])).
% 3.26/1.56  tff(c_699, plain, (![A_115]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_relat_1(k5_relat_1(A_115, k1_xboole_0))) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_696, c_647])).
% 3.26/1.56  tff(c_734, plain, (![A_118]: (v1_xboole_0(k2_relat_1(k5_relat_1(A_118, k1_xboole_0))) | ~v1_relat_1(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_699])).
% 3.26/1.56  tff(c_28, plain, (![A_18]: (~v1_xboole_0(k2_relat_1(A_18)) | ~v1_relat_1(A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.56  tff(c_1077, plain, (![A_144]: (~v1_relat_1(k5_relat_1(A_144, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_144, k1_xboole_0)) | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_734, c_28])).
% 3.26/1.56  tff(c_572, plain, (![B_89, A_90]: (~v1_xboole_0(B_89) | B_89=A_90 | ~v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.26/1.56  tff(c_575, plain, (![A_90]: (k1_xboole_0=A_90 | ~v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_12, c_572])).
% 3.26/1.56  tff(c_1095, plain, (![A_145]: (k5_relat_1(A_145, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_145, k1_xboole_0)) | ~v1_relat_1(A_145))), inference(resolution, [status(thm)], [c_1077, c_575])).
% 3.26/1.56  tff(c_1099, plain, (![A_15]: (k5_relat_1(A_15, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_24, c_1095])).
% 3.26/1.56  tff(c_1103, plain, (![A_146]: (k5_relat_1(A_146, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_146))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_1099])).
% 3.26/1.56  tff(c_1118, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_1103])).
% 3.26/1.56  tff(c_1126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_566, c_1118])).
% 3.26/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.56  
% 3.26/1.56  Inference rules
% 3.26/1.56  ----------------------
% 3.26/1.56  #Ref     : 0
% 3.26/1.56  #Sup     : 248
% 3.26/1.56  #Fact    : 0
% 3.26/1.56  #Define  : 0
% 3.26/1.56  #Split   : 3
% 3.26/1.56  #Chain   : 0
% 3.26/1.56  #Close   : 0
% 3.26/1.56  
% 3.26/1.56  Ordering : KBO
% 3.26/1.56  
% 3.26/1.56  Simplification rules
% 3.26/1.56  ----------------------
% 3.26/1.56  #Subsume      : 53
% 3.26/1.56  #Demod        : 122
% 3.26/1.56  #Tautology    : 74
% 3.26/1.56  #SimpNegUnit  : 2
% 3.26/1.56  #BackRed      : 0
% 3.26/1.56  
% 3.26/1.56  #Partial instantiations: 0
% 3.26/1.56  #Strategies tried      : 1
% 3.26/1.56  
% 3.26/1.56  Timing (in seconds)
% 3.26/1.56  ----------------------
% 3.26/1.56  Preprocessing        : 0.31
% 3.26/1.56  Parsing              : 0.17
% 3.26/1.56  CNF conversion       : 0.02
% 3.26/1.56  Main loop            : 0.44
% 3.26/1.56  Inferencing          : 0.17
% 3.26/1.56  Reduction            : 0.11
% 3.26/1.56  Demodulation         : 0.07
% 3.26/1.56  BG Simplification    : 0.02
% 3.26/1.56  Subsumption          : 0.10
% 3.26/1.56  Abstraction          : 0.02
% 3.26/1.56  MUC search           : 0.00
% 3.26/1.57  Cooper               : 0.00
% 3.26/1.57  Total                : 0.78
% 3.26/1.57  Index Insertion      : 0.00
% 3.26/1.57  Index Deletion       : 0.00
% 3.26/1.57  Index Matching       : 0.00
% 3.26/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
