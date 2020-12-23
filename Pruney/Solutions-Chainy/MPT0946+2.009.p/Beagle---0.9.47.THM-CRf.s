%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:32 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 319 expanded)
%              Number of leaves         :   31 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  165 ( 848 expanded)
%              Number of equality atoms :   17 ( 114 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

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

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_97,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_95,axiom,(
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

tff(f_106,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_56,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_110,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(c_42,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_48,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_46,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_ordinal1(B_2,A_1)
      | r1_ordinal1(A_1,B_2)
      | ~ v3_ordinal1(B_2)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [A_24] : v1_relat_1(k1_wellord2(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_98,plain,(
    ! [B_46,A_47] :
      ( r4_wellord1(B_46,A_47)
      | ~ r4_wellord1(A_47,B_46)
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_100,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_103,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_100])).

tff(c_40,plain,(
    ! [B_30,A_29] :
      ( k2_wellord1(k1_wellord2(B_30),A_29) = k1_wellord2(A_29)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    ! [A_16] :
      ( k3_relat_1(k1_wellord2(A_16)) = A_16
      | ~ v1_relat_1(k1_wellord2(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_54,plain,(
    ! [A_16] : k3_relat_1(k1_wellord2(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28])).

tff(c_36,plain,(
    ! [B_27,A_25] :
      ( k1_wellord1(k1_wellord2(B_27),A_25) = A_25
      | ~ r2_hidden(A_25,B_27)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_250,plain,(
    ! [A_70,B_71] :
      ( ~ r4_wellord1(A_70,k2_wellord1(A_70,k1_wellord1(A_70,B_71)))
      | ~ r2_hidden(B_71,k3_relat_1(A_70))
      | ~ v2_wellord1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_253,plain,(
    ! [B_27,A_25] :
      ( ~ r4_wellord1(k1_wellord2(B_27),k2_wellord1(k1_wellord2(B_27),A_25))
      | ~ r2_hidden(A_25,k3_relat_1(k1_wellord2(B_27)))
      | ~ v2_wellord1(k1_wellord2(B_27))
      | ~ v1_relat_1(k1_wellord2(B_27))
      | ~ r2_hidden(A_25,B_27)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_250])).

tff(c_267,plain,(
    ! [B_75,A_76] :
      ( ~ r4_wellord1(k1_wellord2(B_75),k2_wellord1(k1_wellord2(B_75),A_76))
      | ~ v2_wellord1(k1_wellord2(B_75))
      | ~ r2_hidden(A_76,B_75)
      | ~ v3_ordinal1(B_75)
      | ~ v3_ordinal1(A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_54,c_253])).

tff(c_271,plain,(
    ! [B_77,A_78] :
      ( ~ r4_wellord1(k1_wellord2(B_77),k1_wellord2(A_78))
      | ~ v2_wellord1(k1_wellord2(B_77))
      | ~ r2_hidden(A_78,B_77)
      | ~ v3_ordinal1(B_77)
      | ~ v3_ordinal1(A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_267])).

tff(c_274,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_271])).

tff(c_280,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_274])).

tff(c_284,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_287,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_284])).

tff(c_290,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_287])).

tff(c_326,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_290])).

tff(c_332,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_326])).

tff(c_277,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_271])).

tff(c_283,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_277])).

tff(c_343,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_346,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_343])).

tff(c_350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_332,c_346])).

tff(c_352,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_134,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,A_51)
      | B_50 = A_51
      | r2_hidden(A_51,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_141,plain,(
    ! [A_51,B_50] :
      ( ~ r1_tarski(A_51,B_50)
      | B_50 = A_51
      | r2_hidden(A_51,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_51) ) ),
    inference(resolution,[status(thm)],[c_134,c_10])).

tff(c_38,plain,(
    ! [A_28] :
      ( v2_wellord1(k1_wellord2(A_28))
      | ~ v3_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_351,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_372,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_375,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_372])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_375])).

tff(c_380,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_410,plain,
    ( ~ r1_tarski('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_380])).

tff(c_415,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_352,c_410])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_415])).

tff(c_419,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_418,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_453,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_418])).

tff(c_456,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_453])).

tff(c_460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_456])).

tff(c_461,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_465,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_461])).

tff(c_474,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_419,c_465])).

tff(c_476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:20:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.31  %$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.22/1.31  
% 2.22/1.31  %Foreground sorts:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Background operators:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Foreground operators:
% 2.22/1.31  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.22/1.31  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.22/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.31  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.22/1.31  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.22/1.31  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.22/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.31  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.31  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.22/1.31  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.22/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.31  
% 2.62/1.33  tff(f_124, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 2.62/1.33  tff(f_33, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 2.62/1.33  tff(f_41, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.62/1.33  tff(f_97, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.62/1.33  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 2.62/1.33  tff(f_114, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 2.62/1.33  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 2.62/1.33  tff(f_106, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 2.62/1.33  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 2.62/1.33  tff(f_56, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.62/1.33  tff(f_61, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.62/1.33  tff(f_110, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 2.62/1.33  tff(c_42, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.62/1.33  tff(c_48, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.62/1.33  tff(c_46, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.62/1.33  tff(c_2, plain, (![B_2, A_1]: (r1_ordinal1(B_2, A_1) | r1_ordinal1(A_1, B_2) | ~v3_ordinal1(B_2) | ~v3_ordinal1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.33  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.62/1.33  tff(c_34, plain, (![A_24]: (v1_relat_1(k1_wellord2(A_24)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.62/1.33  tff(c_44, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.62/1.33  tff(c_98, plain, (![B_46, A_47]: (r4_wellord1(B_46, A_47) | ~r4_wellord1(A_47, B_46) | ~v1_relat_1(B_46) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.62/1.33  tff(c_100, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_98])).
% 2.62/1.33  tff(c_103, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_100])).
% 2.62/1.33  tff(c_40, plain, (![B_30, A_29]: (k2_wellord1(k1_wellord2(B_30), A_29)=k1_wellord2(A_29) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.62/1.33  tff(c_28, plain, (![A_16]: (k3_relat_1(k1_wellord2(A_16))=A_16 | ~v1_relat_1(k1_wellord2(A_16)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.62/1.33  tff(c_54, plain, (![A_16]: (k3_relat_1(k1_wellord2(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28])).
% 2.62/1.33  tff(c_36, plain, (![B_27, A_25]: (k1_wellord1(k1_wellord2(B_27), A_25)=A_25 | ~r2_hidden(A_25, B_27) | ~v3_ordinal1(B_27) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.62/1.33  tff(c_250, plain, (![A_70, B_71]: (~r4_wellord1(A_70, k2_wellord1(A_70, k1_wellord1(A_70, B_71))) | ~r2_hidden(B_71, k3_relat_1(A_70)) | ~v2_wellord1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.62/1.33  tff(c_253, plain, (![B_27, A_25]: (~r4_wellord1(k1_wellord2(B_27), k2_wellord1(k1_wellord2(B_27), A_25)) | ~r2_hidden(A_25, k3_relat_1(k1_wellord2(B_27))) | ~v2_wellord1(k1_wellord2(B_27)) | ~v1_relat_1(k1_wellord2(B_27)) | ~r2_hidden(A_25, B_27) | ~v3_ordinal1(B_27) | ~v3_ordinal1(A_25))), inference(superposition, [status(thm), theory('equality')], [c_36, c_250])).
% 2.62/1.33  tff(c_267, plain, (![B_75, A_76]: (~r4_wellord1(k1_wellord2(B_75), k2_wellord1(k1_wellord2(B_75), A_76)) | ~v2_wellord1(k1_wellord2(B_75)) | ~r2_hidden(A_76, B_75) | ~v3_ordinal1(B_75) | ~v3_ordinal1(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_54, c_253])).
% 2.62/1.33  tff(c_271, plain, (![B_77, A_78]: (~r4_wellord1(k1_wellord2(B_77), k1_wellord2(A_78)) | ~v2_wellord1(k1_wellord2(B_77)) | ~r2_hidden(A_78, B_77) | ~v3_ordinal1(B_77) | ~v3_ordinal1(A_78) | ~r1_tarski(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_40, c_267])).
% 2.62/1.33  tff(c_274, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_103, c_271])).
% 2.62/1.33  tff(c_280, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_274])).
% 2.62/1.33  tff(c_284, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_280])).
% 2.62/1.33  tff(c_287, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_284])).
% 2.62/1.33  tff(c_290, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_287])).
% 2.62/1.33  tff(c_326, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_290])).
% 2.62/1.33  tff(c_332, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_326])).
% 2.62/1.33  tff(c_277, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_271])).
% 2.62/1.33  tff(c_283, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_277])).
% 2.62/1.33  tff(c_343, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_283])).
% 2.62/1.33  tff(c_346, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_343])).
% 2.62/1.33  tff(c_350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_332, c_346])).
% 2.62/1.33  tff(c_352, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_283])).
% 2.62/1.33  tff(c_134, plain, (![B_50, A_51]: (r2_hidden(B_50, A_51) | B_50=A_51 | r2_hidden(A_51, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.62/1.33  tff(c_10, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.62/1.33  tff(c_141, plain, (![A_51, B_50]: (~r1_tarski(A_51, B_50) | B_50=A_51 | r2_hidden(A_51, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_51))), inference(resolution, [status(thm)], [c_134, c_10])).
% 2.62/1.33  tff(c_38, plain, (![A_28]: (v2_wellord1(k1_wellord2(A_28)) | ~v3_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.62/1.33  tff(c_351, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_283])).
% 2.62/1.33  tff(c_372, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitLeft, [status(thm)], [c_351])).
% 2.62/1.33  tff(c_375, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_372])).
% 2.62/1.33  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_375])).
% 2.62/1.33  tff(c_380, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_351])).
% 2.62/1.33  tff(c_410, plain, (~r1_tarski('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_141, c_380])).
% 2.62/1.33  tff(c_415, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_352, c_410])).
% 2.62/1.33  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_415])).
% 2.62/1.33  tff(c_419, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_280])).
% 2.62/1.33  tff(c_418, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_280])).
% 2.62/1.33  tff(c_453, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_418])).
% 2.62/1.33  tff(c_456, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_453])).
% 2.62/1.33  tff(c_460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_456])).
% 2.62/1.33  tff(c_461, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_418])).
% 2.62/1.33  tff(c_465, plain, (~r1_tarski('#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_141, c_461])).
% 2.62/1.33  tff(c_474, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_419, c_465])).
% 2.62/1.33  tff(c_476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_474])).
% 2.62/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.33  
% 2.62/1.33  Inference rules
% 2.62/1.33  ----------------------
% 2.62/1.33  #Ref     : 0
% 2.62/1.33  #Sup     : 70
% 2.62/1.33  #Fact    : 4
% 2.62/1.33  #Define  : 0
% 2.62/1.33  #Split   : 4
% 2.62/1.33  #Chain   : 0
% 2.62/1.33  #Close   : 0
% 2.62/1.33  
% 2.62/1.33  Ordering : KBO
% 2.62/1.33  
% 2.62/1.33  Simplification rules
% 2.62/1.33  ----------------------
% 2.62/1.33  #Subsume      : 7
% 2.62/1.33  #Demod        : 109
% 2.62/1.33  #Tautology    : 33
% 2.62/1.33  #SimpNegUnit  : 8
% 2.62/1.33  #BackRed      : 0
% 2.62/1.33  
% 2.62/1.33  #Partial instantiations: 0
% 2.62/1.33  #Strategies tried      : 1
% 2.62/1.33  
% 2.62/1.33  Timing (in seconds)
% 2.62/1.33  ----------------------
% 2.62/1.33  Preprocessing        : 0.31
% 2.62/1.33  Parsing              : 0.17
% 2.62/1.33  CNF conversion       : 0.02
% 2.62/1.33  Main loop            : 0.25
% 2.62/1.33  Inferencing          : 0.09
% 2.62/1.33  Reduction            : 0.08
% 2.62/1.33  Demodulation         : 0.06
% 2.62/1.33  BG Simplification    : 0.02
% 2.62/1.33  Subsumption          : 0.05
% 2.62/1.33  Abstraction          : 0.01
% 2.62/1.33  MUC search           : 0.00
% 2.62/1.33  Cooper               : 0.00
% 2.62/1.33  Total                : 0.60
% 2.62/1.33  Index Insertion      : 0.00
% 2.62/1.33  Index Deletion       : 0.00
% 2.62/1.33  Index Matching       : 0.00
% 2.62/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
