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
% DateTime   : Thu Dec  3 10:06:20 EST 2020

% Result     : Theorem 6.51s
% Output     : CNFRefutation 6.51s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 178 expanded)
%              Number of leaves         :   39 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 339 expanded)
%              Number of equality atoms :   17 (  39 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_88,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_69,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_71,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_62,plain,(
    ! [A_51] : r2_hidden(A_51,k1_ordinal1(A_51)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_72,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_70,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_80,plain,
    ( r2_hidden('#skF_4',k1_ordinal1('#skF_5'))
    | r1_ordinal1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_110,plain,(
    r1_ordinal1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_60,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ r1_ordinal1(A_49,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_101,plain,(
    ! [A_65] :
      ( v1_ordinal1(A_65)
      | ~ v3_ordinal1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_109,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_101])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r2_xboole_0(A_7,B_8)
      | B_8 = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_454,plain,(
    ! [A_124,B_125] :
      ( r2_hidden(A_124,B_125)
      | ~ r2_xboole_0(A_124,B_125)
      | ~ v3_ordinal1(B_125)
      | ~ v1_ordinal1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3263,plain,(
    ! [A_331,B_332] :
      ( r2_hidden(A_331,B_332)
      | ~ v3_ordinal1(B_332)
      | ~ v1_ordinal1(A_331)
      | B_332 = A_331
      | ~ r1_tarski(A_331,B_332) ) ),
    inference(resolution,[status(thm)],[c_20,c_454])).

tff(c_50,plain,(
    ! [A_44] : k2_xboole_0(A_44,k1_tarski(A_44)) = k1_ordinal1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_207,plain,(
    ! [D_87,A_88,B_89] :
      ( ~ r2_hidden(D_87,A_88)
      | r2_hidden(D_87,k2_xboole_0(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_223,plain,(
    ! [D_90,A_91] :
      ( ~ r2_hidden(D_90,A_91)
      | r2_hidden(D_90,k1_ordinal1(A_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_207])).

tff(c_74,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_4',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_134,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_74])).

tff(c_235,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_223,c_134])).

tff(c_3608,plain,
    ( ~ v3_ordinal1('#skF_5')
    | ~ v1_ordinal1('#skF_4')
    | '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_3263,c_235])).

tff(c_3722,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_70,c_3608])).

tff(c_3730,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3722])).

tff(c_3733,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3730])).

tff(c_3737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_110,c_3733])).

tff(c_3738,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3722])).

tff(c_3743,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3738,c_134])).

tff(c_3750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3743])).

tff(c_3752,plain,(
    ~ r1_ordinal1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_108,plain,(
    v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_101])).

tff(c_3751,plain,(
    r2_hidden('#skF_4',k1_ordinal1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_4485,plain,(
    ! [D_425,B_426,A_427] :
      ( r2_hidden(D_425,B_426)
      | r2_hidden(D_425,A_427)
      | ~ r2_hidden(D_425,k2_xboole_0(A_427,B_426)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6149,plain,(
    ! [D_574,A_575] :
      ( r2_hidden(D_574,k1_tarski(A_575))
      | r2_hidden(D_574,A_575)
      | ~ r2_hidden(D_574,k1_ordinal1(A_575)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_4485])).

tff(c_26,plain,(
    ! [A_9] : k2_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3794,plain,(
    ! [A_342,B_343] : k3_tarski(k2_tarski(A_342,B_343)) = k2_xboole_0(A_342,B_343) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3803,plain,(
    ! [A_11] : k3_tarski(k1_tarski(A_11)) = k2_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3794])).

tff(c_3806,plain,(
    ! [A_11] : k3_tarski(k1_tarski(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3803])).

tff(c_3826,plain,(
    ! [A_348,B_349] :
      ( r1_tarski(A_348,k3_tarski(B_349))
      | ~ r2_hidden(A_348,B_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3837,plain,(
    ! [A_348,A_11] :
      ( r1_tarski(A_348,A_11)
      | ~ r2_hidden(A_348,k1_tarski(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3806,c_3826])).

tff(c_6713,plain,(
    ! [D_587,A_588] :
      ( r1_tarski(D_587,A_588)
      | r2_hidden(D_587,A_588)
      | ~ r2_hidden(D_587,k1_ordinal1(A_588)) ) ),
    inference(resolution,[status(thm)],[c_6149,c_3837])).

tff(c_6773,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_3751,c_6713])).

tff(c_6775,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6773])).

tff(c_52,plain,(
    ! [B_48,A_45] :
      ( r1_tarski(B_48,A_45)
      | ~ r2_hidden(B_48,A_45)
      | ~ v1_ordinal1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6778,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6775,c_52])).

tff(c_6784,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_6778])).

tff(c_58,plain,(
    ! [A_49,B_50] :
      ( r1_ordinal1(A_49,B_50)
      | ~ r1_tarski(A_49,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6794,plain,
    ( r1_ordinal1('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6784,c_58])).

tff(c_6797,plain,(
    r1_ordinal1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_6794])).

tff(c_6799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3752,c_6797])).

tff(c_6800,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_6773])).

tff(c_6804,plain,
    ( r1_ordinal1('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6800,c_58])).

tff(c_6807,plain,(
    r1_ordinal1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_6804])).

tff(c_6809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3752,c_6807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:22:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.51/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.35  
% 6.51/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.35  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 6.51/2.35  
% 6.51/2.35  %Foreground sorts:
% 6.51/2.35  
% 6.51/2.35  
% 6.51/2.35  %Background operators:
% 6.51/2.35  
% 6.51/2.35  
% 6.51/2.35  %Foreground operators:
% 6.51/2.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.51/2.35  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.51/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.51/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.51/2.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.51/2.35  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 6.51/2.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.51/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.51/2.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.51/2.35  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 6.51/2.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.51/2.35  tff('#skF_5', type, '#skF_5': $i).
% 6.51/2.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.51/2.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.51/2.35  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.51/2.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.51/2.35  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 6.51/2.35  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.51/2.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.51/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.51/2.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.51/2.35  tff('#skF_4', type, '#skF_4': $i).
% 6.51/2.35  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.51/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.51/2.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.51/2.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.51/2.35  
% 6.51/2.36  tff(f_88, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 6.51/2.36  tff(f_121, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 6.51/2.36  tff(f_86, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 6.51/2.36  tff(f_69, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 6.51/2.36  tff(f_41, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 6.51/2.36  tff(f_97, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 6.51/2.36  tff(f_71, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 6.51/2.36  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.51/2.36  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.51/2.36  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.51/2.36  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.51/2.36  tff(f_61, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.51/2.36  tff(f_78, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 6.51/2.36  tff(c_62, plain, (![A_51]: (r2_hidden(A_51, k1_ordinal1(A_51)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.51/2.36  tff(c_72, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.51/2.36  tff(c_70, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.51/2.36  tff(c_80, plain, (r2_hidden('#skF_4', k1_ordinal1('#skF_5')) | r1_ordinal1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.51/2.36  tff(c_110, plain, (r1_ordinal1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_80])).
% 6.51/2.36  tff(c_60, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~r1_ordinal1(A_49, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_49))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.51/2.36  tff(c_101, plain, (![A_65]: (v1_ordinal1(A_65) | ~v3_ordinal1(A_65))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.51/2.36  tff(c_109, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_101])).
% 6.51/2.36  tff(c_20, plain, (![A_7, B_8]: (r2_xboole_0(A_7, B_8) | B_8=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.51/2.36  tff(c_454, plain, (![A_124, B_125]: (r2_hidden(A_124, B_125) | ~r2_xboole_0(A_124, B_125) | ~v3_ordinal1(B_125) | ~v1_ordinal1(A_124))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.51/2.36  tff(c_3263, plain, (![A_331, B_332]: (r2_hidden(A_331, B_332) | ~v3_ordinal1(B_332) | ~v1_ordinal1(A_331) | B_332=A_331 | ~r1_tarski(A_331, B_332))), inference(resolution, [status(thm)], [c_20, c_454])).
% 6.51/2.36  tff(c_50, plain, (![A_44]: (k2_xboole_0(A_44, k1_tarski(A_44))=k1_ordinal1(A_44))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.51/2.36  tff(c_207, plain, (![D_87, A_88, B_89]: (~r2_hidden(D_87, A_88) | r2_hidden(D_87, k2_xboole_0(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.51/2.36  tff(c_223, plain, (![D_90, A_91]: (~r2_hidden(D_90, A_91) | r2_hidden(D_90, k1_ordinal1(A_91)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_207])).
% 6.51/2.36  tff(c_74, plain, (~r1_ordinal1('#skF_4', '#skF_5') | ~r2_hidden('#skF_4', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.51/2.36  tff(c_134, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_74])).
% 6.51/2.36  tff(c_235, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_223, c_134])).
% 6.51/2.36  tff(c_3608, plain, (~v3_ordinal1('#skF_5') | ~v1_ordinal1('#skF_4') | '#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_3263, c_235])).
% 6.51/2.36  tff(c_3722, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_70, c_3608])).
% 6.51/2.36  tff(c_3730, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_3722])).
% 6.51/2.36  tff(c_3733, plain, (~r1_ordinal1('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_3730])).
% 6.51/2.36  tff(c_3737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_110, c_3733])).
% 6.51/2.36  tff(c_3738, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_3722])).
% 6.51/2.36  tff(c_3743, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3738, c_134])).
% 6.51/2.36  tff(c_3750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_3743])).
% 6.51/2.36  tff(c_3752, plain, (~r1_ordinal1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_80])).
% 6.51/2.36  tff(c_108, plain, (v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_101])).
% 6.51/2.36  tff(c_3751, plain, (r2_hidden('#skF_4', k1_ordinal1('#skF_5'))), inference(splitRight, [status(thm)], [c_80])).
% 6.51/2.36  tff(c_4485, plain, (![D_425, B_426, A_427]: (r2_hidden(D_425, B_426) | r2_hidden(D_425, A_427) | ~r2_hidden(D_425, k2_xboole_0(A_427, B_426)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.51/2.36  tff(c_6149, plain, (![D_574, A_575]: (r2_hidden(D_574, k1_tarski(A_575)) | r2_hidden(D_574, A_575) | ~r2_hidden(D_574, k1_ordinal1(A_575)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_4485])).
% 6.51/2.36  tff(c_26, plain, (![A_9]: (k2_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.51/2.36  tff(c_28, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.51/2.36  tff(c_3794, plain, (![A_342, B_343]: (k3_tarski(k2_tarski(A_342, B_343))=k2_xboole_0(A_342, B_343))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.51/2.36  tff(c_3803, plain, (![A_11]: (k3_tarski(k1_tarski(A_11))=k2_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_28, c_3794])).
% 6.51/2.36  tff(c_3806, plain, (![A_11]: (k3_tarski(k1_tarski(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3803])).
% 6.51/2.36  tff(c_3826, plain, (![A_348, B_349]: (r1_tarski(A_348, k3_tarski(B_349)) | ~r2_hidden(A_348, B_349))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.51/2.36  tff(c_3837, plain, (![A_348, A_11]: (r1_tarski(A_348, A_11) | ~r2_hidden(A_348, k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_3806, c_3826])).
% 6.51/2.36  tff(c_6713, plain, (![D_587, A_588]: (r1_tarski(D_587, A_588) | r2_hidden(D_587, A_588) | ~r2_hidden(D_587, k1_ordinal1(A_588)))), inference(resolution, [status(thm)], [c_6149, c_3837])).
% 6.51/2.36  tff(c_6773, plain, (r1_tarski('#skF_4', '#skF_5') | r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_3751, c_6713])).
% 6.51/2.36  tff(c_6775, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_6773])).
% 6.51/2.36  tff(c_52, plain, (![B_48, A_45]: (r1_tarski(B_48, A_45) | ~r2_hidden(B_48, A_45) | ~v1_ordinal1(A_45))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.51/2.36  tff(c_6778, plain, (r1_tarski('#skF_4', '#skF_5') | ~v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_6775, c_52])).
% 6.51/2.36  tff(c_6784, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_6778])).
% 6.51/2.36  tff(c_58, plain, (![A_49, B_50]: (r1_ordinal1(A_49, B_50) | ~r1_tarski(A_49, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_49))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.51/2.36  tff(c_6794, plain, (r1_ordinal1('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_6784, c_58])).
% 6.51/2.36  tff(c_6797, plain, (r1_ordinal1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_6794])).
% 6.51/2.36  tff(c_6799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3752, c_6797])).
% 6.51/2.36  tff(c_6800, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_6773])).
% 6.51/2.36  tff(c_6804, plain, (r1_ordinal1('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_6800, c_58])).
% 6.51/2.36  tff(c_6807, plain, (r1_ordinal1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_6804])).
% 6.51/2.36  tff(c_6809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3752, c_6807])).
% 6.51/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.36  
% 6.51/2.36  Inference rules
% 6.51/2.36  ----------------------
% 6.51/2.36  #Ref     : 0
% 6.51/2.36  #Sup     : 1400
% 6.51/2.36  #Fact    : 12
% 6.51/2.36  #Define  : 0
% 6.51/2.36  #Split   : 7
% 6.51/2.36  #Chain   : 0
% 6.51/2.36  #Close   : 0
% 6.51/2.36  
% 6.51/2.36  Ordering : KBO
% 6.51/2.36  
% 6.51/2.36  Simplification rules
% 6.51/2.36  ----------------------
% 6.51/2.36  #Subsume      : 214
% 6.51/2.36  #Demod        : 84
% 6.51/2.36  #Tautology    : 80
% 6.51/2.36  #SimpNegUnit  : 23
% 6.51/2.36  #BackRed      : 8
% 6.51/2.36  
% 6.51/2.36  #Partial instantiations: 0
% 6.51/2.36  #Strategies tried      : 1
% 6.51/2.36  
% 6.51/2.36  Timing (in seconds)
% 6.51/2.36  ----------------------
% 6.51/2.37  Preprocessing        : 0.37
% 6.51/2.37  Parsing              : 0.19
% 6.51/2.37  CNF conversion       : 0.03
% 6.51/2.37  Main loop            : 1.18
% 6.51/2.37  Inferencing          : 0.38
% 6.51/2.37  Reduction            : 0.33
% 6.51/2.37  Demodulation         : 0.20
% 6.51/2.37  BG Simplification    : 0.06
% 6.51/2.37  Subsumption          : 0.31
% 6.51/2.37  Abstraction          : 0.06
% 6.51/2.37  MUC search           : 0.00
% 6.51/2.37  Cooper               : 0.00
% 6.51/2.37  Total                : 1.59
% 6.51/2.37  Index Insertion      : 0.00
% 6.51/2.37  Index Deletion       : 0.00
% 6.51/2.37  Index Matching       : 0.00
% 6.51/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
