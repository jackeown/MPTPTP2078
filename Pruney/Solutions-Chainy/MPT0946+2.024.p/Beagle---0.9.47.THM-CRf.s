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
% DateTime   : Thu Dec  3 10:10:35 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 362 expanded)
%              Number of leaves         :   31 ( 141 expanded)
%              Depth                    :   15
%              Number of atoms          :  167 ( 970 expanded)
%              Number of equality atoms :   24 ( 144 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_116,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_62,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_xboole_0(A,B)
              & A != B
              & ~ r2_xboole_0(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_103,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_112,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_47,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_44,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_50,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_48,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    ! [A_29] :
      ( v2_wellord1(k1_wellord2(A_29))
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_156,plain,(
    ! [B_51,A_52] :
      ( r2_xboole_0(B_51,A_52)
      | B_51 = A_52
      | r2_xboole_0(A_52,B_51)
      | ~ v3_ordinal1(B_51)
      | ~ v3_ordinal1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_174,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | r2_xboole_0(B_56,A_55)
      | B_56 = A_55
      | ~ v3_ordinal1(B_56)
      | ~ v3_ordinal1(A_55) ) ),
    inference(resolution,[status(thm)],[c_156,c_6])).

tff(c_182,plain,(
    ! [B_56,A_55] :
      ( r1_tarski(B_56,A_55)
      | r1_tarski(A_55,B_56)
      | B_56 = A_55
      | ~ v3_ordinal1(B_56)
      | ~ v3_ordinal1(A_55) ) ),
    inference(resolution,[status(thm)],[c_174,c_6])).

tff(c_36,plain,(
    ! [A_25] : v1_relat_1(k1_wellord2(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_91,plain,(
    ! [B_45,A_46] :
      ( r4_wellord1(B_45,A_46)
      | ~ r4_wellord1(A_46,B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_93,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_91])).

tff(c_96,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_93])).

tff(c_42,plain,(
    ! [B_31,A_30] :
      ( k2_wellord1(k1_wellord2(B_31),A_30) = k1_wellord2(A_30)
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    ! [A_17] :
      ( k3_relat_1(k1_wellord2(A_17)) = A_17
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    ! [A_17] : k3_relat_1(k1_wellord2(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30])).

tff(c_38,plain,(
    ! [B_28,A_26] :
      ( k1_wellord1(k1_wellord2(B_28),A_26) = A_26
      | ~ r2_hidden(A_26,B_28)
      | ~ v3_ordinal1(B_28)
      | ~ v3_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_278,plain,(
    ! [A_68,B_69] :
      ( ~ r4_wellord1(A_68,k2_wellord1(A_68,k1_wellord1(A_68,B_69)))
      | ~ r2_hidden(B_69,k3_relat_1(A_68))
      | ~ v2_wellord1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_281,plain,(
    ! [B_28,A_26] :
      ( ~ r4_wellord1(k1_wellord2(B_28),k2_wellord1(k1_wellord2(B_28),A_26))
      | ~ r2_hidden(A_26,k3_relat_1(k1_wellord2(B_28)))
      | ~ v2_wellord1(k1_wellord2(B_28))
      | ~ v1_relat_1(k1_wellord2(B_28))
      | ~ r2_hidden(A_26,B_28)
      | ~ v3_ordinal1(B_28)
      | ~ v3_ordinal1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_278])).

tff(c_341,plain,(
    ! [B_77,A_78] :
      ( ~ r4_wellord1(k1_wellord2(B_77),k2_wellord1(k1_wellord2(B_77),A_78))
      | ~ v2_wellord1(k1_wellord2(B_77))
      | ~ r2_hidden(A_78,B_77)
      | ~ v3_ordinal1(B_77)
      | ~ v3_ordinal1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_56,c_281])).

tff(c_345,plain,(
    ! [B_79,A_80] :
      ( ~ r4_wellord1(k1_wellord2(B_79),k1_wellord2(A_80))
      | ~ v2_wellord1(k1_wellord2(B_79))
      | ~ r2_hidden(A_80,B_79)
      | ~ v3_ordinal1(B_79)
      | ~ v3_ordinal1(A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_341])).

tff(c_348,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_345])).

tff(c_354,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_348])).

tff(c_358,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_354])).

tff(c_387,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_182,c_358])).

tff(c_393,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_387])).

tff(c_394,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_393])).

tff(c_127,plain,(
    ! [B_49,A_50] :
      ( r2_hidden(B_49,A_50)
      | B_49 = A_50
      | r2_hidden(A_50,B_49)
      | ~ v3_ordinal1(B_49)
      | ~ v3_ordinal1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_134,plain,(
    ! [A_50,B_49] :
      ( ~ r1_tarski(A_50,B_49)
      | B_49 = A_50
      | r2_hidden(A_50,B_49)
      | ~ v3_ordinal1(B_49)
      | ~ v3_ordinal1(A_50) ) ),
    inference(resolution,[status(thm)],[c_127,c_12])).

tff(c_351,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_345])).

tff(c_357,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_351])).

tff(c_407,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_357])).

tff(c_408,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_407])).

tff(c_411,plain,
    ( ~ r1_tarski('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_134,c_408])).

tff(c_416,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_394,c_411])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_416])).

tff(c_419,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_423,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_419])).

tff(c_427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_423])).

tff(c_429,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_428,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_438,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_428])).

tff(c_467,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_438])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_467])).

tff(c_472,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_428])).

tff(c_476,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_472])).

tff(c_485,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_429,c_476])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_485])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.74  
% 2.98/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.74  %$ r4_wellord1 > r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.98/1.74  
% 2.98/1.74  %Foreground sorts:
% 2.98/1.74  
% 2.98/1.74  
% 2.98/1.74  %Background operators:
% 2.98/1.74  
% 2.98/1.74  
% 2.98/1.74  %Foreground operators:
% 2.98/1.74  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 2.98/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.74  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.98/1.74  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.98/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.74  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.98/1.74  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.98/1.74  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.74  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.98/1.74  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.98/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.74  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.74  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.98/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.98/1.74  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.98/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.98/1.74  
% 3.29/1.77  tff(f_130, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 3.29/1.77  tff(f_116, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 3.29/1.77  tff(f_62, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_ordinal1)).
% 3.29/1.77  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.29/1.77  tff(f_103, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.29/1.77  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 3.29/1.77  tff(f_120, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 3.29/1.77  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 3.29/1.77  tff(f_112, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 3.29/1.77  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 3.29/1.77  tff(f_47, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.29/1.77  tff(f_67, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.29/1.77  tff(c_44, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.29/1.77  tff(c_50, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.29/1.77  tff(c_48, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.29/1.77  tff(c_40, plain, (![A_29]: (v2_wellord1(k1_wellord2(A_29)) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.29/1.77  tff(c_156, plain, (![B_51, A_52]: (r2_xboole_0(B_51, A_52) | B_51=A_52 | r2_xboole_0(A_52, B_51) | ~v3_ordinal1(B_51) | ~v3_ordinal1(A_52))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.29/1.77  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.77  tff(c_174, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | r2_xboole_0(B_56, A_55) | B_56=A_55 | ~v3_ordinal1(B_56) | ~v3_ordinal1(A_55))), inference(resolution, [status(thm)], [c_156, c_6])).
% 3.29/1.77  tff(c_182, plain, (![B_56, A_55]: (r1_tarski(B_56, A_55) | r1_tarski(A_55, B_56) | B_56=A_55 | ~v3_ordinal1(B_56) | ~v3_ordinal1(A_55))), inference(resolution, [status(thm)], [c_174, c_6])).
% 3.29/1.77  tff(c_36, plain, (![A_25]: (v1_relat_1(k1_wellord2(A_25)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.29/1.77  tff(c_46, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.29/1.77  tff(c_91, plain, (![B_45, A_46]: (r4_wellord1(B_45, A_46) | ~r4_wellord1(A_46, B_45) | ~v1_relat_1(B_45) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.29/1.77  tff(c_93, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_91])).
% 3.29/1.77  tff(c_96, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_93])).
% 3.29/1.77  tff(c_42, plain, (![B_31, A_30]: (k2_wellord1(k1_wellord2(B_31), A_30)=k1_wellord2(A_30) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.29/1.77  tff(c_30, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17 | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.77  tff(c_56, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30])).
% 3.29/1.77  tff(c_38, plain, (![B_28, A_26]: (k1_wellord1(k1_wellord2(B_28), A_26)=A_26 | ~r2_hidden(A_26, B_28) | ~v3_ordinal1(B_28) | ~v3_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.29/1.77  tff(c_278, plain, (![A_68, B_69]: (~r4_wellord1(A_68, k2_wellord1(A_68, k1_wellord1(A_68, B_69))) | ~r2_hidden(B_69, k3_relat_1(A_68)) | ~v2_wellord1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.29/1.77  tff(c_281, plain, (![B_28, A_26]: (~r4_wellord1(k1_wellord2(B_28), k2_wellord1(k1_wellord2(B_28), A_26)) | ~r2_hidden(A_26, k3_relat_1(k1_wellord2(B_28))) | ~v2_wellord1(k1_wellord2(B_28)) | ~v1_relat_1(k1_wellord2(B_28)) | ~r2_hidden(A_26, B_28) | ~v3_ordinal1(B_28) | ~v3_ordinal1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_38, c_278])).
% 3.29/1.77  tff(c_341, plain, (![B_77, A_78]: (~r4_wellord1(k1_wellord2(B_77), k2_wellord1(k1_wellord2(B_77), A_78)) | ~v2_wellord1(k1_wellord2(B_77)) | ~r2_hidden(A_78, B_77) | ~v3_ordinal1(B_77) | ~v3_ordinal1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_56, c_281])).
% 3.29/1.77  tff(c_345, plain, (![B_79, A_80]: (~r4_wellord1(k1_wellord2(B_79), k1_wellord2(A_80)) | ~v2_wellord1(k1_wellord2(B_79)) | ~r2_hidden(A_80, B_79) | ~v3_ordinal1(B_79) | ~v3_ordinal1(A_80) | ~r1_tarski(A_80, B_79))), inference(superposition, [status(thm), theory('equality')], [c_42, c_341])).
% 3.29/1.77  tff(c_348, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_96, c_345])).
% 3.29/1.77  tff(c_354, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_348])).
% 3.29/1.77  tff(c_358, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_354])).
% 3.29/1.77  tff(c_387, plain, (r1_tarski('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_182, c_358])).
% 3.29/1.77  tff(c_393, plain, (r1_tarski('#skF_4', '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_387])).
% 3.29/1.77  tff(c_394, plain, (r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_393])).
% 3.29/1.77  tff(c_127, plain, (![B_49, A_50]: (r2_hidden(B_49, A_50) | B_49=A_50 | r2_hidden(A_50, B_49) | ~v3_ordinal1(B_49) | ~v3_ordinal1(A_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.29/1.77  tff(c_12, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.29/1.77  tff(c_134, plain, (![A_50, B_49]: (~r1_tarski(A_50, B_49) | B_49=A_50 | r2_hidden(A_50, B_49) | ~v3_ordinal1(B_49) | ~v3_ordinal1(A_50))), inference(resolution, [status(thm)], [c_127, c_12])).
% 3.29/1.77  tff(c_351, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_345])).
% 3.29/1.77  tff(c_357, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_351])).
% 3.29/1.77  tff(c_407, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_394, c_357])).
% 3.29/1.77  tff(c_408, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_407])).
% 3.29/1.77  tff(c_411, plain, (~r1_tarski('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_134, c_408])).
% 3.29/1.77  tff(c_416, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_394, c_411])).
% 3.29/1.77  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_416])).
% 3.29/1.77  tff(c_419, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_407])).
% 3.29/1.77  tff(c_423, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_419])).
% 3.29/1.77  tff(c_427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_423])).
% 3.29/1.77  tff(c_429, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_354])).
% 3.29/1.77  tff(c_428, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_354])).
% 3.29/1.77  tff(c_438, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_428])).
% 3.29/1.77  tff(c_467, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_438])).
% 3.29/1.77  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_467])).
% 3.29/1.77  tff(c_472, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_428])).
% 3.29/1.77  tff(c_476, plain, (~r1_tarski('#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_134, c_472])).
% 3.29/1.77  tff(c_485, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_429, c_476])).
% 3.29/1.77  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_485])).
% 3.29/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.77  
% 3.29/1.77  Inference rules
% 3.29/1.77  ----------------------
% 3.29/1.77  #Ref     : 0
% 3.29/1.77  #Sup     : 67
% 3.29/1.77  #Fact    : 6
% 3.29/1.77  #Define  : 0
% 3.29/1.77  #Split   : 3
% 3.29/1.77  #Chain   : 0
% 3.29/1.77  #Close   : 0
% 3.29/1.77  
% 3.29/1.77  Ordering : KBO
% 3.29/1.77  
% 3.29/1.77  Simplification rules
% 3.29/1.77  ----------------------
% 3.29/1.77  #Subsume      : 3
% 3.29/1.77  #Demod        : 106
% 3.29/1.77  #Tautology    : 41
% 3.29/1.77  #SimpNegUnit  : 8
% 3.29/1.77  #BackRed      : 0
% 3.29/1.77  
% 3.29/1.77  #Partial instantiations: 0
% 3.29/1.77  #Strategies tried      : 1
% 3.29/1.77  
% 3.29/1.77  Timing (in seconds)
% 3.29/1.77  ----------------------
% 3.29/1.78  Preprocessing        : 0.51
% 3.29/1.78  Parsing              : 0.26
% 3.29/1.78  CNF conversion       : 0.04
% 3.35/1.78  Main loop            : 0.44
% 3.35/1.78  Inferencing          : 0.16
% 3.35/1.78  Reduction            : 0.14
% 3.35/1.78  Demodulation         : 0.10
% 3.35/1.78  BG Simplification    : 0.03
% 3.35/1.78  Subsumption          : 0.09
% 3.35/1.78  Abstraction          : 0.02
% 3.35/1.78  MUC search           : 0.00
% 3.35/1.78  Cooper               : 0.00
% 3.35/1.78  Total                : 1.01
% 3.35/1.78  Index Insertion      : 0.00
% 3.35/1.78  Index Deletion       : 0.00
% 3.35/1.78  Index Matching       : 0.00
% 3.35/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
