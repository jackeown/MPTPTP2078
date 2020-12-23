%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:32 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 340 expanded)
%              Number of leaves         :   31 ( 133 expanded)
%              Depth                    :   12
%              Number of atoms          :  178 ( 894 expanded)
%              Number of equality atoms :   15 ( 111 expanded)
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

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_92,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_101,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_56,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_105,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_46,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_50,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_52,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_ordinal1(A_5,B_6)
      | ~ v3_ordinal1(B_6)
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    ! [A_24] : v1_relat_1(k1_wellord2(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_88,plain,(
    ! [B_40,A_41] :
      ( r4_wellord1(B_40,A_41)
      | ~ r4_wellord1(A_41,B_40)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_90,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_88])).

tff(c_93,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_90])).

tff(c_44,plain,(
    ! [B_30,A_29] :
      ( k2_wellord1(k1_wellord2(B_30),A_29) = k1_wellord2(A_29)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    ! [A_16] :
      ( k3_relat_1(k1_wellord2(A_16)) = A_16
      | ~ v1_relat_1(k1_wellord2(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_58,plain,(
    ! [A_16] : k3_relat_1(k1_wellord2(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32])).

tff(c_40,plain,(
    ! [B_27,A_25] :
      ( k1_wellord1(k1_wellord2(B_27),A_25) = A_25
      | ~ r2_hidden(A_25,B_27)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_181,plain,(
    ! [A_59,B_60] :
      ( ~ r4_wellord1(A_59,k2_wellord1(A_59,k1_wellord1(A_59,B_60)))
      | ~ r2_hidden(B_60,k3_relat_1(A_59))
      | ~ v2_wellord1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_184,plain,(
    ! [B_27,A_25] :
      ( ~ r4_wellord1(k1_wellord2(B_27),k2_wellord1(k1_wellord2(B_27),A_25))
      | ~ r2_hidden(A_25,k3_relat_1(k1_wellord2(B_27)))
      | ~ v2_wellord1(k1_wellord2(B_27))
      | ~ v1_relat_1(k1_wellord2(B_27))
      | ~ r2_hidden(A_25,B_27)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_181])).

tff(c_203,plain,(
    ! [B_67,A_68] :
      ( ~ r4_wellord1(k1_wellord2(B_67),k2_wellord1(k1_wellord2(B_67),A_68))
      | ~ v2_wellord1(k1_wellord2(B_67))
      | ~ r2_hidden(A_68,B_67)
      | ~ v3_ordinal1(B_67)
      | ~ v3_ordinal1(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_184])).

tff(c_207,plain,(
    ! [B_69,A_70] :
      ( ~ r4_wellord1(k1_wellord2(B_69),k1_wellord2(A_70))
      | ~ v2_wellord1(k1_wellord2(B_69))
      | ~ r2_hidden(A_70,B_69)
      | ~ v3_ordinal1(B_69)
      | ~ v3_ordinal1(A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_203])).

tff(c_210,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_93,c_207])).

tff(c_216,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_210])).

tff(c_220,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_271,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_220])).

tff(c_274,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_271])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( r2_hidden(B_9,A_7)
      | r1_ordinal1(A_7,B_9)
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    ! [A_28] :
      ( v2_wellord1(k1_wellord2(A_28))
      | ~ v3_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_213,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_207])).

tff(c_219,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_213])).

tff(c_221,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_230,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_221])).

tff(c_233,plain,(
    ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_230])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_ordinal1(B_4,A_3)
      | r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_224,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_220])).

tff(c_227,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_224])).

tff(c_239,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_227])).

tff(c_245,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_239])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_245])).

tff(c_249,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_312,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_315,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_312])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_315])).

tff(c_320,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_351,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_320])).

tff(c_354,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_351])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_354])).

tff(c_358,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_121,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ r1_ordinal1(A_49,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [B_50,A_49] :
      ( B_50 = A_49
      | ~ r1_tarski(B_50,A_49)
      | ~ r1_ordinal1(A_49,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_49) ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_361,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_358,c_128])).

tff(c_369,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_361])).

tff(c_370,plain,(
    ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_369])).

tff(c_357,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_391,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_394,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_391])).

tff(c_398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_394])).

tff(c_399,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_403,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_399])).

tff(c_406,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_403])).

tff(c_408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.33  
% 2.53/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.34  %$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.53/1.34  
% 2.53/1.34  %Foreground sorts:
% 2.53/1.34  
% 2.53/1.34  
% 2.53/1.34  %Background operators:
% 2.53/1.34  
% 2.53/1.34  
% 2.53/1.34  %Foreground operators:
% 2.53/1.34  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 2.53/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.53/1.34  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.53/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.34  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.53/1.34  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.53/1.34  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.53/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.34  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.53/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.34  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.53/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.53/1.34  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.53/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.53/1.34  
% 2.53/1.35  tff(f_119, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 2.53/1.35  tff(f_47, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.53/1.35  tff(f_92, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.53/1.35  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 2.53/1.35  tff(f_109, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 2.53/1.35  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 2.53/1.35  tff(f_101, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 2.53/1.35  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 2.53/1.35  tff(f_56, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.53/1.35  tff(f_105, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 2.53/1.35  tff(f_39, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 2.53/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.53/1.35  tff(c_46, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.53/1.35  tff(c_50, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.53/1.35  tff(c_52, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.53/1.35  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~r1_ordinal1(A_5, B_6) | ~v3_ordinal1(B_6) | ~v3_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.35  tff(c_38, plain, (![A_24]: (v1_relat_1(k1_wellord2(A_24)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.53/1.35  tff(c_48, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.53/1.35  tff(c_88, plain, (![B_40, A_41]: (r4_wellord1(B_40, A_41) | ~r4_wellord1(A_41, B_40) | ~v1_relat_1(B_40) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.53/1.35  tff(c_90, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_88])).
% 2.53/1.35  tff(c_93, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_90])).
% 2.53/1.35  tff(c_44, plain, (![B_30, A_29]: (k2_wellord1(k1_wellord2(B_30), A_29)=k1_wellord2(A_29) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.53/1.35  tff(c_32, plain, (![A_16]: (k3_relat_1(k1_wellord2(A_16))=A_16 | ~v1_relat_1(k1_wellord2(A_16)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.53/1.35  tff(c_58, plain, (![A_16]: (k3_relat_1(k1_wellord2(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32])).
% 2.53/1.35  tff(c_40, plain, (![B_27, A_25]: (k1_wellord1(k1_wellord2(B_27), A_25)=A_25 | ~r2_hidden(A_25, B_27) | ~v3_ordinal1(B_27) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.53/1.35  tff(c_181, plain, (![A_59, B_60]: (~r4_wellord1(A_59, k2_wellord1(A_59, k1_wellord1(A_59, B_60))) | ~r2_hidden(B_60, k3_relat_1(A_59)) | ~v2_wellord1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.35  tff(c_184, plain, (![B_27, A_25]: (~r4_wellord1(k1_wellord2(B_27), k2_wellord1(k1_wellord2(B_27), A_25)) | ~r2_hidden(A_25, k3_relat_1(k1_wellord2(B_27))) | ~v2_wellord1(k1_wellord2(B_27)) | ~v1_relat_1(k1_wellord2(B_27)) | ~r2_hidden(A_25, B_27) | ~v3_ordinal1(B_27) | ~v3_ordinal1(A_25))), inference(superposition, [status(thm), theory('equality')], [c_40, c_181])).
% 2.53/1.35  tff(c_203, plain, (![B_67, A_68]: (~r4_wellord1(k1_wellord2(B_67), k2_wellord1(k1_wellord2(B_67), A_68)) | ~v2_wellord1(k1_wellord2(B_67)) | ~r2_hidden(A_68, B_67) | ~v3_ordinal1(B_67) | ~v3_ordinal1(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_184])).
% 2.53/1.35  tff(c_207, plain, (![B_69, A_70]: (~r4_wellord1(k1_wellord2(B_69), k1_wellord2(A_70)) | ~v2_wellord1(k1_wellord2(B_69)) | ~r2_hidden(A_70, B_69) | ~v3_ordinal1(B_69) | ~v3_ordinal1(A_70) | ~r1_tarski(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_44, c_203])).
% 2.53/1.35  tff(c_210, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_93, c_207])).
% 2.53/1.35  tff(c_216, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_210])).
% 2.53/1.35  tff(c_220, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_216])).
% 2.53/1.35  tff(c_271, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_220])).
% 2.53/1.35  tff(c_274, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_271])).
% 2.53/1.35  tff(c_14, plain, (![B_9, A_7]: (r2_hidden(B_9, A_7) | r1_ordinal1(A_7, B_9) | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.53/1.35  tff(c_42, plain, (![A_28]: (v2_wellord1(k1_wellord2(A_28)) | ~v3_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.53/1.35  tff(c_213, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_207])).
% 2.53/1.35  tff(c_219, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_213])).
% 2.53/1.35  tff(c_221, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_219])).
% 2.53/1.35  tff(c_230, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_221])).
% 2.53/1.35  tff(c_233, plain, (~r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_230])).
% 2.53/1.35  tff(c_8, plain, (![B_4, A_3]: (r1_ordinal1(B_4, A_3) | r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.53/1.35  tff(c_224, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_220])).
% 2.53/1.35  tff(c_227, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_224])).
% 2.53/1.35  tff(c_239, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_227])).
% 2.53/1.35  tff(c_245, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_239])).
% 2.53/1.35  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_245])).
% 2.53/1.35  tff(c_249, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_219])).
% 2.53/1.35  tff(c_312, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitLeft, [status(thm)], [c_249])).
% 2.53/1.35  tff(c_315, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_312])).
% 2.53/1.35  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_315])).
% 2.53/1.35  tff(c_320, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_249])).
% 2.53/1.35  tff(c_351, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_320])).
% 2.53/1.35  tff(c_354, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_351])).
% 2.53/1.35  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_274, c_354])).
% 2.53/1.35  tff(c_358, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_216])).
% 2.53/1.35  tff(c_121, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~r1_ordinal1(A_49, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.35  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.35  tff(c_128, plain, (![B_50, A_49]: (B_50=A_49 | ~r1_tarski(B_50, A_49) | ~r1_ordinal1(A_49, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_49))), inference(resolution, [status(thm)], [c_121, c_2])).
% 2.53/1.35  tff(c_361, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_358, c_128])).
% 2.53/1.35  tff(c_369, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_361])).
% 2.53/1.35  tff(c_370, plain, (~r1_ordinal1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_369])).
% 2.53/1.35  tff(c_357, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_216])).
% 2.53/1.35  tff(c_391, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_357])).
% 2.53/1.35  tff(c_394, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_391])).
% 2.53/1.35  tff(c_398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_394])).
% 2.53/1.35  tff(c_399, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_357])).
% 2.53/1.35  tff(c_403, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_399])).
% 2.53/1.35  tff(c_406, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_403])).
% 2.53/1.35  tff(c_408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_406])).
% 2.53/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.35  
% 2.53/1.35  Inference rules
% 2.53/1.35  ----------------------
% 2.53/1.35  #Ref     : 0
% 2.53/1.35  #Sup     : 56
% 2.53/1.35  #Fact    : 2
% 2.53/1.35  #Define  : 0
% 2.53/1.35  #Split   : 4
% 2.53/1.35  #Chain   : 0
% 2.53/1.35  #Close   : 0
% 2.53/1.35  
% 2.53/1.35  Ordering : KBO
% 2.53/1.35  
% 2.53/1.35  Simplification rules
% 2.53/1.35  ----------------------
% 2.53/1.35  #Subsume      : 7
% 2.53/1.35  #Demod        : 98
% 2.53/1.35  #Tautology    : 30
% 2.53/1.35  #SimpNegUnit  : 9
% 2.53/1.35  #BackRed      : 0
% 2.53/1.35  
% 2.53/1.35  #Partial instantiations: 0
% 2.53/1.35  #Strategies tried      : 1
% 2.53/1.35  
% 2.53/1.35  Timing (in seconds)
% 2.53/1.35  ----------------------
% 2.53/1.36  Preprocessing        : 0.33
% 2.53/1.36  Parsing              : 0.17
% 2.53/1.36  CNF conversion       : 0.02
% 2.53/1.36  Main loop            : 0.25
% 2.53/1.36  Inferencing          : 0.09
% 2.53/1.36  Reduction            : 0.08
% 2.53/1.36  Demodulation         : 0.06
% 2.53/1.36  BG Simplification    : 0.02
% 2.53/1.36  Subsumption          : 0.05
% 2.53/1.36  Abstraction          : 0.01
% 2.53/1.36  MUC search           : 0.00
% 2.53/1.36  Cooper               : 0.00
% 2.53/1.36  Total                : 0.62
% 2.53/1.36  Index Insertion      : 0.00
% 2.53/1.36  Index Deletion       : 0.00
% 2.53/1.36  Index Matching       : 0.00
% 2.53/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
