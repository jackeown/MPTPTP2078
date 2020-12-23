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
% DateTime   : Thu Dec  3 10:06:15 EST 2020

% Result     : Theorem 10.57s
% Output     : CNFRefutation 10.85s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 211 expanded)
%              Number of leaves         :   33 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 450 expanded)
%              Number of equality atoms :   30 ( 118 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_71,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_99,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_52,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    ! [A_59,B_60] : k1_enumset1(A_59,A_59,B_60) = k2_tarski(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [E_17,A_11,B_12] : r2_hidden(E_17,k1_enumset1(A_11,B_12,E_17)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_165,plain,(
    ! [B_61,A_62] : r2_hidden(B_61,k2_tarski(A_62,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_30])).

tff(c_170,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_165])).

tff(c_60,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_tarski(A_22)) = k1_ordinal1(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_213,plain,(
    ! [D_70,B_71,A_72] :
      ( ~ r2_hidden(D_70,B_71)
      | r2_hidden(D_70,k2_xboole_0(A_72,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1058,plain,(
    ! [D_154,A_155] :
      ( ~ r2_hidden(D_154,k1_tarski(A_155))
      | r2_hidden(D_154,k1_ordinal1(A_155)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_213])).

tff(c_1067,plain,(
    ! [A_18] : r2_hidden(A_18,k1_ordinal1(A_18)) ),
    inference(resolution,[status(thm)],[c_170,c_1058])).

tff(c_72,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_70,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_80,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_100,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_64,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ r1_ordinal1(A_23,B_24)
      | ~ v3_ordinal1(B_24)
      | ~ v3_ordinal1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_82,plain,(
    ! [A_33] :
      ( v1_ordinal1(A_33)
      | ~ v3_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_90,plain,(
    v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_82])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r2_xboole_0(A_9,B_10)
      | B_10 = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_318,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(A_84,B_85)
      | ~ r2_xboole_0(A_84,B_85)
      | ~ v3_ordinal1(B_85)
      | ~ v1_ordinal1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3785,plain,(
    ! [A_377,B_378] :
      ( r2_hidden(A_377,B_378)
      | ~ v3_ordinal1(B_378)
      | ~ v1_ordinal1(A_377)
      | B_378 = A_377
      | ~ r1_tarski(A_377,B_378) ) ),
    inference(resolution,[status(thm)],[c_22,c_318])).

tff(c_176,plain,(
    ! [D_64,A_65,B_66] :
      ( ~ r2_hidden(D_64,A_65)
      | r2_hidden(D_64,k2_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_324,plain,(
    ! [D_87,A_88] :
      ( ~ r2_hidden(D_87,A_88)
      | r2_hidden(D_87,k1_ordinal1(A_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_176])).

tff(c_74,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_135,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_74])).

tff(c_374,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_324,c_135])).

tff(c_4177,plain,
    ( ~ v3_ordinal1('#skF_6')
    | ~ v1_ordinal1('#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_3785,c_374])).

tff(c_4326,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_70,c_4177])).

tff(c_4341,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4326])).

tff(c_4344,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_4341])).

tff(c_4348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_100,c_4344])).

tff(c_4349,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4326])).

tff(c_4353,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4349,c_135])).

tff(c_4360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1067,c_4353])).

tff(c_4362,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_4361,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_5110,plain,(
    ! [D_477,B_478,A_479] :
      ( r2_hidden(D_477,B_478)
      | r2_hidden(D_477,A_479)
      | ~ r2_hidden(D_477,k2_xboole_0(A_479,B_478)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5123,plain,(
    ! [D_477,A_22] :
      ( r2_hidden(D_477,k1_tarski(A_22))
      | r2_hidden(D_477,A_22)
      | ~ r2_hidden(D_477,k1_ordinal1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_5110])).

tff(c_54,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5222,plain,(
    ! [E_488,C_489,B_490,A_491] :
      ( E_488 = C_489
      | E_488 = B_490
      | E_488 = A_491
      | ~ r2_hidden(E_488,k1_enumset1(A_491,B_490,C_489)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7986,plain,(
    ! [E_718,B_719,A_720] :
      ( E_718 = B_719
      | E_718 = A_720
      | E_718 = A_720
      | ~ r2_hidden(E_718,k2_tarski(A_720,B_719)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_5222])).

tff(c_17479,plain,(
    ! [E_1349,A_1350] :
      ( E_1349 = A_1350
      | E_1349 = A_1350
      | E_1349 = A_1350
      | ~ r2_hidden(E_1349,k1_tarski(A_1350)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_7986])).

tff(c_17564,plain,(
    ! [D_1351,A_1352] :
      ( D_1351 = A_1352
      | r2_hidden(D_1351,A_1352)
      | ~ r2_hidden(D_1351,k1_ordinal1(A_1352)) ) ),
    inference(resolution,[status(thm)],[c_5123,c_17479])).

tff(c_17652,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_4361,c_17564])).

tff(c_17653,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_17652])).

tff(c_4657,plain,(
    ! [B_433,A_434] :
      ( r2_hidden(B_433,A_434)
      | r1_ordinal1(A_434,B_433)
      | ~ v3_ordinal1(B_433)
      | ~ v3_ordinal1(A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4720,plain,(
    ! [A_434,B_433] :
      ( ~ r2_hidden(A_434,B_433)
      | r1_ordinal1(A_434,B_433)
      | ~ v3_ordinal1(B_433)
      | ~ v3_ordinal1(A_434) ) ),
    inference(resolution,[status(thm)],[c_4657,c_2])).

tff(c_17656,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_17653,c_4720])).

tff(c_17661,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_17656])).

tff(c_17663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4362,c_17661])).

tff(c_17664,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_17652])).

tff(c_17669,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17664,c_4362])).

tff(c_68,plain,(
    ! [B_30,A_28] :
      ( r2_hidden(B_30,A_28)
      | r1_ordinal1(A_28,B_30)
      | ~ v3_ordinal1(B_30)
      | ~ v3_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_17665,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_17652])).

tff(c_17681,plain,(
    ~ r2_hidden('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17664,c_17665])).

tff(c_17687,plain,
    ( r1_ordinal1('#skF_6','#skF_6')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_17681])).

tff(c_17694,plain,(
    r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_17687])).

tff(c_17695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17669,c_17694])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.57/4.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.57/4.41  
% 10.57/4.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.85/4.41  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 10.85/4.41  
% 10.85/4.41  %Foreground sorts:
% 10.85/4.41  
% 10.85/4.41  
% 10.85/4.41  %Background operators:
% 10.85/4.41  
% 10.85/4.41  
% 10.85/4.41  %Foreground operators:
% 10.85/4.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.85/4.41  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 10.85/4.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.85/4.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.85/4.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.85/4.41  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 10.85/4.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.85/4.41  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 10.85/4.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.85/4.41  tff('#skF_5', type, '#skF_5': $i).
% 10.85/4.41  tff('#skF_6', type, '#skF_6': $i).
% 10.85/4.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.85/4.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.85/4.41  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 10.85/4.41  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 10.85/4.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 10.85/4.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 10.85/4.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.85/4.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.85/4.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 10.85/4.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.85/4.41  
% 10.85/4.43  tff(f_63, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.85/4.43  tff(f_65, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 10.85/4.43  tff(f_61, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 10.85/4.43  tff(f_73, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 10.85/4.43  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 10.85/4.43  tff(f_109, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 10.85/4.43  tff(f_81, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 10.85/4.43  tff(f_71, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 10.85/4.43  tff(f_46, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 10.85/4.43  tff(f_90, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 10.85/4.43  tff(f_99, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 10.85/4.43  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 10.85/4.43  tff(c_52, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.85/4.43  tff(c_138, plain, (![A_59, B_60]: (k1_enumset1(A_59, A_59, B_60)=k2_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.85/4.43  tff(c_30, plain, (![E_17, A_11, B_12]: (r2_hidden(E_17, k1_enumset1(A_11, B_12, E_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.85/4.43  tff(c_165, plain, (![B_61, A_62]: (r2_hidden(B_61, k2_tarski(A_62, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_138, c_30])).
% 10.85/4.43  tff(c_170, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_165])).
% 10.85/4.43  tff(c_60, plain, (![A_22]: (k2_xboole_0(A_22, k1_tarski(A_22))=k1_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.85/4.43  tff(c_213, plain, (![D_70, B_71, A_72]: (~r2_hidden(D_70, B_71) | r2_hidden(D_70, k2_xboole_0(A_72, B_71)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.85/4.43  tff(c_1058, plain, (![D_154, A_155]: (~r2_hidden(D_154, k1_tarski(A_155)) | r2_hidden(D_154, k1_ordinal1(A_155)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_213])).
% 10.85/4.43  tff(c_1067, plain, (![A_18]: (r2_hidden(A_18, k1_ordinal1(A_18)))), inference(resolution, [status(thm)], [c_170, c_1058])).
% 10.85/4.43  tff(c_72, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.85/4.43  tff(c_70, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.85/4.43  tff(c_80, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.85/4.43  tff(c_100, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_80])).
% 10.85/4.43  tff(c_64, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~r1_ordinal1(A_23, B_24) | ~v3_ordinal1(B_24) | ~v3_ordinal1(A_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.85/4.43  tff(c_82, plain, (![A_33]: (v1_ordinal1(A_33) | ~v3_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.85/4.43  tff(c_90, plain, (v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_82])).
% 10.85/4.43  tff(c_22, plain, (![A_9, B_10]: (r2_xboole_0(A_9, B_10) | B_10=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.85/4.43  tff(c_318, plain, (![A_84, B_85]: (r2_hidden(A_84, B_85) | ~r2_xboole_0(A_84, B_85) | ~v3_ordinal1(B_85) | ~v1_ordinal1(A_84))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.85/4.43  tff(c_3785, plain, (![A_377, B_378]: (r2_hidden(A_377, B_378) | ~v3_ordinal1(B_378) | ~v1_ordinal1(A_377) | B_378=A_377 | ~r1_tarski(A_377, B_378))), inference(resolution, [status(thm)], [c_22, c_318])).
% 10.85/4.43  tff(c_176, plain, (![D_64, A_65, B_66]: (~r2_hidden(D_64, A_65) | r2_hidden(D_64, k2_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.85/4.43  tff(c_324, plain, (![D_87, A_88]: (~r2_hidden(D_87, A_88) | r2_hidden(D_87, k1_ordinal1(A_88)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_176])).
% 10.85/4.43  tff(c_74, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.85/4.43  tff(c_135, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_74])).
% 10.85/4.43  tff(c_374, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_324, c_135])).
% 10.85/4.43  tff(c_4177, plain, (~v3_ordinal1('#skF_6') | ~v1_ordinal1('#skF_5') | '#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_3785, c_374])).
% 10.85/4.43  tff(c_4326, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_70, c_4177])).
% 10.85/4.43  tff(c_4341, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_4326])).
% 10.85/4.43  tff(c_4344, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_4341])).
% 10.85/4.43  tff(c_4348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_100, c_4344])).
% 10.85/4.43  tff(c_4349, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_4326])).
% 10.85/4.43  tff(c_4353, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4349, c_135])).
% 10.85/4.43  tff(c_4360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1067, c_4353])).
% 10.85/4.43  tff(c_4362, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_80])).
% 10.85/4.43  tff(c_4361, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_80])).
% 10.85/4.43  tff(c_5110, plain, (![D_477, B_478, A_479]: (r2_hidden(D_477, B_478) | r2_hidden(D_477, A_479) | ~r2_hidden(D_477, k2_xboole_0(A_479, B_478)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.85/4.43  tff(c_5123, plain, (![D_477, A_22]: (r2_hidden(D_477, k1_tarski(A_22)) | r2_hidden(D_477, A_22) | ~r2_hidden(D_477, k1_ordinal1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_5110])).
% 10.85/4.43  tff(c_54, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.85/4.43  tff(c_5222, plain, (![E_488, C_489, B_490, A_491]: (E_488=C_489 | E_488=B_490 | E_488=A_491 | ~r2_hidden(E_488, k1_enumset1(A_491, B_490, C_489)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.85/4.43  tff(c_7986, plain, (![E_718, B_719, A_720]: (E_718=B_719 | E_718=A_720 | E_718=A_720 | ~r2_hidden(E_718, k2_tarski(A_720, B_719)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_5222])).
% 10.85/4.43  tff(c_17479, plain, (![E_1349, A_1350]: (E_1349=A_1350 | E_1349=A_1350 | E_1349=A_1350 | ~r2_hidden(E_1349, k1_tarski(A_1350)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_7986])).
% 10.85/4.43  tff(c_17564, plain, (![D_1351, A_1352]: (D_1351=A_1352 | r2_hidden(D_1351, A_1352) | ~r2_hidden(D_1351, k1_ordinal1(A_1352)))), inference(resolution, [status(thm)], [c_5123, c_17479])).
% 10.85/4.43  tff(c_17652, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_4361, c_17564])).
% 10.85/4.43  tff(c_17653, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_17652])).
% 10.85/4.43  tff(c_4657, plain, (![B_433, A_434]: (r2_hidden(B_433, A_434) | r1_ordinal1(A_434, B_433) | ~v3_ordinal1(B_433) | ~v3_ordinal1(A_434))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.85/4.43  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 10.85/4.43  tff(c_4720, plain, (![A_434, B_433]: (~r2_hidden(A_434, B_433) | r1_ordinal1(A_434, B_433) | ~v3_ordinal1(B_433) | ~v3_ordinal1(A_434))), inference(resolution, [status(thm)], [c_4657, c_2])).
% 10.85/4.43  tff(c_17656, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_17653, c_4720])).
% 10.85/4.43  tff(c_17661, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_17656])).
% 10.85/4.43  tff(c_17663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4362, c_17661])).
% 10.85/4.43  tff(c_17664, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_17652])).
% 10.85/4.43  tff(c_17669, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_17664, c_4362])).
% 10.85/4.43  tff(c_68, plain, (![B_30, A_28]: (r2_hidden(B_30, A_28) | r1_ordinal1(A_28, B_30) | ~v3_ordinal1(B_30) | ~v3_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.85/4.43  tff(c_17665, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_17652])).
% 10.85/4.43  tff(c_17681, plain, (~r2_hidden('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_17664, c_17665])).
% 10.85/4.43  tff(c_17687, plain, (r1_ordinal1('#skF_6', '#skF_6') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_17681])).
% 10.85/4.43  tff(c_17694, plain, (r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_17687])).
% 10.85/4.43  tff(c_17695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17669, c_17694])).
% 10.85/4.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.85/4.43  
% 10.85/4.43  Inference rules
% 10.85/4.43  ----------------------
% 10.85/4.43  #Ref     : 0
% 10.85/4.43  #Sup     : 3694
% 10.85/4.43  #Fact    : 12
% 10.85/4.43  #Define  : 0
% 10.85/4.43  #Split   : 7
% 10.85/4.43  #Chain   : 0
% 10.85/4.43  #Close   : 0
% 10.85/4.43  
% 10.85/4.43  Ordering : KBO
% 10.85/4.43  
% 10.85/4.43  Simplification rules
% 10.85/4.43  ----------------------
% 10.85/4.43  #Subsume      : 843
% 10.85/4.43  #Demod        : 62
% 10.85/4.43  #Tautology    : 77
% 10.85/4.43  #SimpNegUnit  : 70
% 10.85/4.43  #BackRed      : 16
% 10.85/4.43  
% 10.85/4.43  #Partial instantiations: 0
% 10.85/4.43  #Strategies tried      : 1
% 10.85/4.43  
% 10.85/4.43  Timing (in seconds)
% 10.85/4.43  ----------------------
% 10.85/4.43  Preprocessing        : 0.52
% 10.85/4.43  Parsing              : 0.25
% 10.85/4.43  CNF conversion       : 0.04
% 10.85/4.43  Main loop            : 3.01
% 10.85/4.43  Inferencing          : 0.73
% 10.85/4.43  Reduction            : 0.91
% 10.85/4.43  Demodulation         : 0.49
% 10.85/4.43  BG Simplification    : 0.10
% 10.85/4.43  Subsumption          : 1.01
% 10.85/4.43  Abstraction          : 0.12
% 10.85/4.43  MUC search           : 0.00
% 10.85/4.43  Cooper               : 0.00
% 10.85/4.43  Total                : 3.58
% 10.85/4.43  Index Insertion      : 0.00
% 10.85/4.43  Index Deletion       : 0.00
% 10.85/4.43  Index Matching       : 0.00
% 10.85/4.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
