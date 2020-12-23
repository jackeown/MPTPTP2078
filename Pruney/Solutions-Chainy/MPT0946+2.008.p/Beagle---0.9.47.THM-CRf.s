%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:32 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 448 expanded)
%              Number of leaves         :   31 ( 171 expanded)
%              Depth                    :   15
%              Number of atoms          :  177 (1201 expanded)
%              Number of equality atoms :   14 ( 154 expanded)
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

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_114,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_65,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_101,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_99,axiom,(
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

tff(f_110,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_56,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(c_48,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    ! [A_29] :
      ( v2_wellord1(k1_wellord2(A_29))
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( r2_hidden(B_10,A_8)
      | r1_ordinal1(A_8,B_10)
      | ~ v3_ordinal1(B_10)
      | ~ v3_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [A_25] : v1_relat_1(k1_wellord2(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_98,plain,(
    ! [B_47,A_48] :
      ( r4_wellord1(B_47,A_48)
      | ~ r4_wellord1(A_48,B_47)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_100,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_103,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_100])).

tff(c_40,plain,(
    ! [B_31,A_30] :
      ( k2_wellord1(k1_wellord2(B_31),A_30) = k1_wellord2(A_30)
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    ! [A_17] :
      ( k3_relat_1(k1_wellord2(A_17)) = A_17
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_54,plain,(
    ! [A_17] : k3_relat_1(k1_wellord2(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28])).

tff(c_36,plain,(
    ! [B_28,A_26] :
      ( k1_wellord1(k1_wellord2(B_28),A_26) = A_26
      | ~ r2_hidden(A_26,B_28)
      | ~ v3_ordinal1(B_28)
      | ~ v3_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_175,plain,(
    ! [A_61,B_62] :
      ( ~ r4_wellord1(A_61,k2_wellord1(A_61,k1_wellord1(A_61,B_62)))
      | ~ r2_hidden(B_62,k3_relat_1(A_61))
      | ~ v2_wellord1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_178,plain,(
    ! [B_28,A_26] :
      ( ~ r4_wellord1(k1_wellord2(B_28),k2_wellord1(k1_wellord2(B_28),A_26))
      | ~ r2_hidden(A_26,k3_relat_1(k1_wellord2(B_28)))
      | ~ v2_wellord1(k1_wellord2(B_28))
      | ~ v1_relat_1(k1_wellord2(B_28))
      | ~ r2_hidden(A_26,B_28)
      | ~ v3_ordinal1(B_28)
      | ~ v3_ordinal1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_175])).

tff(c_187,plain,(
    ! [B_63,A_64] :
      ( ~ r4_wellord1(k1_wellord2(B_63),k2_wellord1(k1_wellord2(B_63),A_64))
      | ~ v2_wellord1(k1_wellord2(B_63))
      | ~ r2_hidden(A_64,B_63)
      | ~ v3_ordinal1(B_63)
      | ~ v3_ordinal1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_54,c_178])).

tff(c_191,plain,(
    ! [B_65,A_66] :
      ( ~ r4_wellord1(k1_wellord2(B_65),k1_wellord2(A_66))
      | ~ v2_wellord1(k1_wellord2(B_65))
      | ~ r2_hidden(A_66,B_65)
      | ~ v3_ordinal1(B_65)
      | ~ v3_ordinal1(A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_187])).

tff(c_194,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_191])).

tff(c_200,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_194])).

tff(c_222,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_225,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_222])).

tff(c_228,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_225])).

tff(c_197,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_191])).

tff(c_203,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_197])).

tff(c_241,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_244,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_241])).

tff(c_247,plain,(
    ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_244])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_ordinal1(B_2,A_1)
      | r1_ordinal1(A_1,B_2)
      | ~ v3_ordinal1(B_2)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_231,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_228])).

tff(c_237,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_231])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_237])).

tff(c_251,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_298,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_301,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_298])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_301])).

tff(c_306,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_312,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_306])).

tff(c_315,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_312])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_315])).

tff(c_318,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_326,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_366,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_326])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_366])).

tff(c_371,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_381,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_371])).

tff(c_392,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_381])).

tff(c_42,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8,plain,(
    ! [B_7,A_5] :
      ( r2_hidden(B_7,A_5)
      | B_7 = A_5
      | r2_hidden(A_5,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_375,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_371])).

tff(c_384,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_375])).

tff(c_385,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_384])).

tff(c_395,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_203])).

tff(c_396,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_395])).

tff(c_399,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_396])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_392,c_399])).

tff(c_404,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_395])).

tff(c_408,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_404])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.35  
% 2.34/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.36  %$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.34/1.36  
% 2.34/1.36  %Foreground sorts:
% 2.34/1.36  
% 2.34/1.36  
% 2.34/1.36  %Background operators:
% 2.34/1.36  
% 2.34/1.36  
% 2.34/1.36  %Foreground operators:
% 2.34/1.36  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 2.34/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.34/1.36  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.34/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.36  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.34/1.36  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.34/1.36  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.34/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.36  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.34/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.36  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.34/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.34/1.36  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.34/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.34/1.36  
% 2.60/1.38  tff(f_128, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 2.60/1.38  tff(f_114, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 2.60/1.38  tff(f_65, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.60/1.38  tff(f_41, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.60/1.38  tff(f_101, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.60/1.38  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 2.60/1.38  tff(f_118, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 2.60/1.38  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 2.60/1.38  tff(f_110, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 2.60/1.38  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 2.60/1.38  tff(f_33, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 2.60/1.38  tff(f_56, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.60/1.38  tff(c_48, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.60/1.38  tff(c_38, plain, (![A_29]: (v2_wellord1(k1_wellord2(A_29)) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.60/1.38  tff(c_46, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.60/1.38  tff(c_10, plain, (![B_10, A_8]: (r2_hidden(B_10, A_8) | r1_ordinal1(A_8, B_10) | ~v3_ordinal1(B_10) | ~v3_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.60/1.38  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.60/1.38  tff(c_34, plain, (![A_25]: (v1_relat_1(k1_wellord2(A_25)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.60/1.38  tff(c_44, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.60/1.38  tff(c_98, plain, (![B_47, A_48]: (r4_wellord1(B_47, A_48) | ~r4_wellord1(A_48, B_47) | ~v1_relat_1(B_47) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.60/1.38  tff(c_100, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_98])).
% 2.60/1.38  tff(c_103, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_100])).
% 2.60/1.38  tff(c_40, plain, (![B_31, A_30]: (k2_wellord1(k1_wellord2(B_31), A_30)=k1_wellord2(A_30) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.60/1.38  tff(c_28, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17 | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.60/1.38  tff(c_54, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28])).
% 2.60/1.38  tff(c_36, plain, (![B_28, A_26]: (k1_wellord1(k1_wellord2(B_28), A_26)=A_26 | ~r2_hidden(A_26, B_28) | ~v3_ordinal1(B_28) | ~v3_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.60/1.38  tff(c_175, plain, (![A_61, B_62]: (~r4_wellord1(A_61, k2_wellord1(A_61, k1_wellord1(A_61, B_62))) | ~r2_hidden(B_62, k3_relat_1(A_61)) | ~v2_wellord1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.60/1.38  tff(c_178, plain, (![B_28, A_26]: (~r4_wellord1(k1_wellord2(B_28), k2_wellord1(k1_wellord2(B_28), A_26)) | ~r2_hidden(A_26, k3_relat_1(k1_wellord2(B_28))) | ~v2_wellord1(k1_wellord2(B_28)) | ~v1_relat_1(k1_wellord2(B_28)) | ~r2_hidden(A_26, B_28) | ~v3_ordinal1(B_28) | ~v3_ordinal1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_36, c_175])).
% 2.60/1.38  tff(c_187, plain, (![B_63, A_64]: (~r4_wellord1(k1_wellord2(B_63), k2_wellord1(k1_wellord2(B_63), A_64)) | ~v2_wellord1(k1_wellord2(B_63)) | ~r2_hidden(A_64, B_63) | ~v3_ordinal1(B_63) | ~v3_ordinal1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_54, c_178])).
% 2.60/1.38  tff(c_191, plain, (![B_65, A_66]: (~r4_wellord1(k1_wellord2(B_65), k1_wellord2(A_66)) | ~v2_wellord1(k1_wellord2(B_65)) | ~r2_hidden(A_66, B_65) | ~v3_ordinal1(B_65) | ~v3_ordinal1(A_66) | ~r1_tarski(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_40, c_187])).
% 2.60/1.38  tff(c_194, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_103, c_191])).
% 2.60/1.38  tff(c_200, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_194])).
% 2.60/1.38  tff(c_222, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_200])).
% 2.60/1.38  tff(c_225, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_222])).
% 2.60/1.38  tff(c_228, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_225])).
% 2.60/1.38  tff(c_197, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_191])).
% 2.60/1.38  tff(c_203, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_197])).
% 2.60/1.38  tff(c_241, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_203])).
% 2.60/1.38  tff(c_244, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_241])).
% 2.60/1.38  tff(c_247, plain, (~r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_244])).
% 2.60/1.38  tff(c_2, plain, (![B_2, A_1]: (r1_ordinal1(B_2, A_1) | r1_ordinal1(A_1, B_2) | ~v3_ordinal1(B_2) | ~v3_ordinal1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.38  tff(c_231, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_228])).
% 2.60/1.38  tff(c_237, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_231])).
% 2.60/1.38  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_237])).
% 2.60/1.38  tff(c_251, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_203])).
% 2.60/1.38  tff(c_298, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitLeft, [status(thm)], [c_251])).
% 2.60/1.38  tff(c_301, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_298])).
% 2.60/1.38  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_301])).
% 2.60/1.38  tff(c_306, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_251])).
% 2.60/1.38  tff(c_312, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_306])).
% 2.60/1.38  tff(c_315, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_312])).
% 2.60/1.38  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_228, c_315])).
% 2.60/1.38  tff(c_318, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_200])).
% 2.60/1.38  tff(c_326, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_318])).
% 2.60/1.38  tff(c_366, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_326])).
% 2.60/1.38  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_366])).
% 2.60/1.38  tff(c_371, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_318])).
% 2.60/1.38  tff(c_381, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_371])).
% 2.60/1.38  tff(c_392, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_381])).
% 2.60/1.38  tff(c_42, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.60/1.38  tff(c_8, plain, (![B_7, A_5]: (r2_hidden(B_7, A_5) | B_7=A_5 | r2_hidden(A_5, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.38  tff(c_375, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_371])).
% 2.60/1.38  tff(c_384, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_375])).
% 2.60/1.38  tff(c_385, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_384])).
% 2.60/1.38  tff(c_395, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_385, c_203])).
% 2.60/1.38  tff(c_396, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_395])).
% 2.60/1.38  tff(c_399, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_396])).
% 2.60/1.38  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_392, c_399])).
% 2.60/1.38  tff(c_404, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_395])).
% 2.60/1.38  tff(c_408, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_404])).
% 2.60/1.38  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_408])).
% 2.60/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.38  
% 2.60/1.38  Inference rules
% 2.60/1.38  ----------------------
% 2.60/1.38  #Ref     : 0
% 2.60/1.38  #Sup     : 53
% 2.60/1.38  #Fact    : 4
% 2.60/1.38  #Define  : 0
% 2.60/1.38  #Split   : 5
% 2.60/1.38  #Chain   : 0
% 2.60/1.38  #Close   : 0
% 2.60/1.38  
% 2.60/1.38  Ordering : KBO
% 2.60/1.38  
% 2.60/1.38  Simplification rules
% 2.60/1.38  ----------------------
% 2.60/1.38  #Subsume      : 1
% 2.60/1.38  #Demod        : 106
% 2.60/1.38  #Tautology    : 31
% 2.60/1.38  #SimpNegUnit  : 4
% 2.60/1.38  #BackRed      : 0
% 2.60/1.38  
% 2.60/1.38  #Partial instantiations: 0
% 2.60/1.38  #Strategies tried      : 1
% 2.60/1.38  
% 2.60/1.38  Timing (in seconds)
% 2.60/1.38  ----------------------
% 2.60/1.38  Preprocessing        : 0.34
% 2.60/1.38  Parsing              : 0.17
% 2.60/1.38  CNF conversion       : 0.03
% 2.60/1.38  Main loop            : 0.26
% 2.60/1.38  Inferencing          : 0.10
% 2.60/1.38  Reduction            : 0.08
% 2.60/1.38  Demodulation         : 0.06
% 2.60/1.38  BG Simplification    : 0.02
% 2.60/1.38  Subsumption          : 0.04
% 2.60/1.38  Abstraction          : 0.01
% 2.60/1.38  MUC search           : 0.00
% 2.60/1.38  Cooper               : 0.00
% 2.60/1.38  Total                : 0.64
% 2.60/1.38  Index Insertion      : 0.00
% 2.60/1.38  Index Deletion       : 0.00
% 2.60/1.38  Index Matching       : 0.00
% 2.60/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
