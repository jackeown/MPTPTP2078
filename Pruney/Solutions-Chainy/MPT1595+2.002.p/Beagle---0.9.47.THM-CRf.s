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
% DateTime   : Thu Dec  3 10:25:20 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 434 expanded)
%              Number of leaves         :   41 ( 172 expanded)
%              Depth                    :   13
%              Number of atoms          :  228 (1006 expanded)
%              Number of equality atoms :    9 ( 170 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_relat_1 > k2_yellow_1 > k1_yellow_1 > k1_wellord2 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
               => ( r3_orders_2(k2_yellow_1(A),B,C)
                <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_103,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_48,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_46,axiom,(
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

tff(f_99,axiom,(
    ! [A] : k1_yellow_1(A) = k1_wellord2(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_50,plain,(
    ! [A_27] : u1_struct_0(k2_yellow_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k2_yellow_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_68,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_67,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56])).

tff(c_38,plain,(
    ! [A_24] : l1_orders_2(k2_yellow_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_60,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_83,plain,(
    ~ r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,
    ( r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_126,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_66])).

tff(c_22,plain,(
    ! [A_11] : v1_relat_1(k1_wellord2(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [C_9,D_10,A_3] :
      ( r2_hidden(k4_tarski(C_9,D_10),k1_wellord2(A_3))
      | ~ r1_tarski(C_9,D_10)
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3)
      | ~ v1_relat_1(k1_wellord2(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    ! [C_9,D_10,A_3] :
      ( r2_hidden(k4_tarski(C_9,D_10),k1_wellord2(A_3))
      | ~ r1_tarski(C_9,D_10)
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18])).

tff(c_48,plain,(
    ! [A_26] : k1_yellow_1(A_26) = k1_wellord2(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_52,plain,(
    ! [A_27] : u1_orders_2(k2_yellow_1(A_27)) = k1_yellow_1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_69,plain,(
    ! [A_27] : u1_orders_2(k2_yellow_1(A_27)) = k1_wellord2(A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52])).

tff(c_172,plain,(
    ! [A_64,B_65,C_66] :
      ( r1_orders_2(A_64,B_65,C_66)
      | ~ r2_hidden(k4_tarski(B_65,C_66),u1_orders_2(A_64))
      | ~ m1_subset_1(C_66,u1_struct_0(A_64))
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_orders_2(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_181,plain,(
    ! [A_27,B_65,C_66] :
      ( r1_orders_2(k2_yellow_1(A_27),B_65,C_66)
      | ~ r2_hidden(k4_tarski(B_65,C_66),k1_wellord2(A_27))
      | ~ m1_subset_1(C_66,u1_struct_0(k2_yellow_1(A_27)))
      | ~ m1_subset_1(B_65,u1_struct_0(k2_yellow_1(A_27)))
      | ~ l1_orders_2(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_172])).

tff(c_186,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_orders_2(k2_yellow_1(A_67),B_68,C_69)
      | ~ r2_hidden(k4_tarski(B_68,C_69),k1_wellord2(A_67))
      | ~ m1_subset_1(C_69,A_67)
      | ~ m1_subset_1(B_68,A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50,c_50,c_181])).

tff(c_220,plain,(
    ! [A_85,C_86,D_87] :
      ( r1_orders_2(k2_yellow_1(A_85),C_86,D_87)
      | ~ m1_subset_1(D_87,A_85)
      | ~ m1_subset_1(C_86,A_85)
      | ~ r1_tarski(C_86,D_87)
      | ~ r2_hidden(D_87,A_85)
      | ~ r2_hidden(C_86,A_85) ) ),
    inference(resolution,[status(thm)],[c_74,c_186])).

tff(c_42,plain,(
    ! [A_25] : v3_orders_2(k2_yellow_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_199,plain,(
    ! [A_70,B_71,C_72] :
      ( r3_orders_2(A_70,B_71,C_72)
      | ~ r1_orders_2(A_70,B_71,C_72)
      | ~ m1_subset_1(C_72,u1_struct_0(A_70))
      | ~ m1_subset_1(B_71,u1_struct_0(A_70))
      | ~ l1_orders_2(A_70)
      | ~ v3_orders_2(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_201,plain,(
    ! [A_27,B_71,C_72] :
      ( r3_orders_2(k2_yellow_1(A_27),B_71,C_72)
      | ~ r1_orders_2(k2_yellow_1(A_27),B_71,C_72)
      | ~ m1_subset_1(C_72,A_27)
      | ~ m1_subset_1(B_71,u1_struct_0(k2_yellow_1(A_27)))
      | ~ l1_orders_2(k2_yellow_1(A_27))
      | ~ v3_orders_2(k2_yellow_1(A_27))
      | v2_struct_0(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_199])).

tff(c_204,plain,(
    ! [A_73,B_74,C_75] :
      ( r3_orders_2(k2_yellow_1(A_73),B_74,C_75)
      | ~ r1_orders_2(k2_yellow_1(A_73),B_74,C_75)
      | ~ m1_subset_1(C_75,A_73)
      | ~ m1_subset_1(B_74,A_73)
      | v2_struct_0(k2_yellow_1(A_73)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_50,c_201])).

tff(c_207,plain,
    ( ~ r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_204,c_83])).

tff(c_210,plain,
    ( ~ r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_68,c_207])).

tff(c_211,plain,(
    ~ r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_226,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_220,c_211])).

tff(c_230,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_67,c_68,c_226])).

tff(c_231,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_234,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_231])).

tff(c_237,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_234])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_237])).

tff(c_240,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_244,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_240])).

tff(c_247,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_244])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_247])).

tff(c_250,plain,(
    v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_121,plain,(
    ! [A_43] :
      ( v1_xboole_0(u1_struct_0(A_43))
      | ~ l1_struct_0(A_43)
      | ~ v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_124,plain,(
    ! [A_27] :
      ( v1_xboole_0(A_27)
      | ~ l1_struct_0(k2_yellow_1(A_27))
      | ~ v2_struct_0(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_121])).

tff(c_254,plain,
    ( v1_xboole_0('#skF_3')
    | ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_250,c_124])).

tff(c_257,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_254])).

tff(c_260,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_257])).

tff(c_264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_260])).

tff(c_265,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_304,plain,(
    r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_66])).

tff(c_385,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_orders_2(A_126,B_127,C_128)
      | ~ r3_orders_2(A_126,B_127,C_128)
      | ~ m1_subset_1(C_128,u1_struct_0(A_126))
      | ~ m1_subset_1(B_127,u1_struct_0(A_126))
      | ~ l1_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_387,plain,
    ( r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0(k2_yellow_1('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_3')))
    | ~ l1_orders_2(k2_yellow_1('#skF_3'))
    | ~ v3_orders_2(k2_yellow_1('#skF_3'))
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_304,c_385])).

tff(c_390,plain,
    ( r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_67,c_50,c_68,c_50,c_387])).

tff(c_391,plain,(
    v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_306,plain,(
    ! [A_93] :
      ( v1_xboole_0(u1_struct_0(A_93))
      | ~ l1_struct_0(A_93)
      | ~ v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_309,plain,(
    ! [A_27] :
      ( v1_xboole_0(A_27)
      | ~ l1_struct_0(k2_yellow_1(A_27))
      | ~ v2_struct_0(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_306])).

tff(c_394,plain,
    ( v1_xboole_0('#skF_3')
    | ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_391,c_309])).

tff(c_397,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_394])).

tff(c_400,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_397])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_400])).

tff(c_405,plain,(
    r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_345,plain,(
    ! [B_108,C_109,A_110] :
      ( r2_hidden(k4_tarski(B_108,C_109),u1_orders_2(A_110))
      | ~ r1_orders_2(A_110,B_108,C_109)
      | ~ m1_subset_1(C_109,u1_struct_0(A_110))
      | ~ m1_subset_1(B_108,u1_struct_0(A_110))
      | ~ l1_orders_2(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_348,plain,(
    ! [B_108,C_109,A_27] :
      ( r2_hidden(k4_tarski(B_108,C_109),k1_wellord2(A_27))
      | ~ r1_orders_2(k2_yellow_1(A_27),B_108,C_109)
      | ~ m1_subset_1(C_109,u1_struct_0(k2_yellow_1(A_27)))
      | ~ m1_subset_1(B_108,u1_struct_0(k2_yellow_1(A_27)))
      | ~ l1_orders_2(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_345])).

tff(c_351,plain,(
    ! [B_111,C_112,A_113] :
      ( r2_hidden(k4_tarski(B_111,C_112),k1_wellord2(A_113))
      | ~ r1_orders_2(k2_yellow_1(A_113),B_111,C_112)
      | ~ m1_subset_1(C_112,A_113)
      | ~ m1_subset_1(B_111,A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50,c_50,c_348])).

tff(c_20,plain,(
    ! [C_9,D_10,A_3] :
      ( r1_tarski(C_9,D_10)
      | ~ r2_hidden(k4_tarski(C_9,D_10),k1_wellord2(A_3))
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3)
      | ~ v1_relat_1(k1_wellord2(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    ! [C_9,D_10,A_3] :
      ( r1_tarski(C_9,D_10)
      | ~ r2_hidden(k4_tarski(C_9,D_10),k1_wellord2(A_3))
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20])).

tff(c_355,plain,(
    ! [B_111,C_112,A_113] :
      ( r1_tarski(B_111,C_112)
      | ~ r2_hidden(C_112,A_113)
      | ~ r2_hidden(B_111,A_113)
      | ~ r1_orders_2(k2_yellow_1(A_113),B_111,C_112)
      | ~ m1_subset_1(C_112,A_113)
      | ~ m1_subset_1(B_111,A_113) ) ),
    inference(resolution,[status(thm)],[c_351,c_72])).

tff(c_409,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_405,c_355])).

tff(c_412,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_68,c_409])).

tff(c_413,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_412])).

tff(c_414,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_417,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_414])).

tff(c_420,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_417])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_420])).

tff(c_423,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_427,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_423])).

tff(c_430,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_427])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:59 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.83  
% 3.33/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.84  %$ r3_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_relat_1 > k2_yellow_1 > k1_yellow_1 > k1_wellord2 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.33/1.84  
% 3.33/1.84  %Foreground sorts:
% 3.33/1.84  
% 3.33/1.84  
% 3.33/1.84  %Background operators:
% 3.33/1.84  
% 3.33/1.84  
% 3.33/1.84  %Foreground operators:
% 3.33/1.84  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.33/1.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.84  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.33/1.84  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.33/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.33/1.84  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.33/1.84  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.33/1.84  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.33/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.84  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.84  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.33/1.84  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.84  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.33/1.84  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.33/1.84  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.33/1.84  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.33/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.84  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.84  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.33/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.33/1.84  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.33/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.33/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.84  
% 3.33/1.87  tff(f_117, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.33/1.87  tff(f_103, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.33/1.87  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.33/1.87  tff(f_89, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.33/1.87  tff(f_70, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.33/1.87  tff(f_48, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.33/1.87  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 3.33/1.87  tff(f_99, axiom, (![A]: (k1_yellow_1(A) = k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_yellow_1)).
% 3.33/1.87  tff(f_66, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 3.33/1.87  tff(f_97, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.33/1.87  tff(f_85, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.33/1.87  tff(f_54, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 3.33/1.87  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.33/1.87  tff(c_50, plain, (![A_27]: (u1_struct_0(k2_yellow_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.33/1.87  tff(c_54, plain, (m1_subset_1('#skF_5', u1_struct_0(k2_yellow_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.33/1.87  tff(c_68, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54])).
% 3.33/1.87  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.87  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.33/1.87  tff(c_67, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56])).
% 3.33/1.87  tff(c_38, plain, (![A_24]: (l1_orders_2(k2_yellow_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.33/1.87  tff(c_30, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.33/1.87  tff(c_60, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.33/1.87  tff(c_83, plain, (~r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 3.33/1.87  tff(c_66, plain, (r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.33/1.87  tff(c_126, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_83, c_66])).
% 3.33/1.87  tff(c_22, plain, (![A_11]: (v1_relat_1(k1_wellord2(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.33/1.87  tff(c_18, plain, (![C_9, D_10, A_3]: (r2_hidden(k4_tarski(C_9, D_10), k1_wellord2(A_3)) | ~r1_tarski(C_9, D_10) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3) | ~v1_relat_1(k1_wellord2(A_3)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.33/1.87  tff(c_74, plain, (![C_9, D_10, A_3]: (r2_hidden(k4_tarski(C_9, D_10), k1_wellord2(A_3)) | ~r1_tarski(C_9, D_10) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18])).
% 3.33/1.87  tff(c_48, plain, (![A_26]: (k1_yellow_1(A_26)=k1_wellord2(A_26))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.33/1.87  tff(c_52, plain, (![A_27]: (u1_orders_2(k2_yellow_1(A_27))=k1_yellow_1(A_27))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.33/1.87  tff(c_69, plain, (![A_27]: (u1_orders_2(k2_yellow_1(A_27))=k1_wellord2(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52])).
% 3.33/1.87  tff(c_172, plain, (![A_64, B_65, C_66]: (r1_orders_2(A_64, B_65, C_66) | ~r2_hidden(k4_tarski(B_65, C_66), u1_orders_2(A_64)) | ~m1_subset_1(C_66, u1_struct_0(A_64)) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l1_orders_2(A_64))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.33/1.87  tff(c_181, plain, (![A_27, B_65, C_66]: (r1_orders_2(k2_yellow_1(A_27), B_65, C_66) | ~r2_hidden(k4_tarski(B_65, C_66), k1_wellord2(A_27)) | ~m1_subset_1(C_66, u1_struct_0(k2_yellow_1(A_27))) | ~m1_subset_1(B_65, u1_struct_0(k2_yellow_1(A_27))) | ~l1_orders_2(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_172])).
% 3.33/1.87  tff(c_186, plain, (![A_67, B_68, C_69]: (r1_orders_2(k2_yellow_1(A_67), B_68, C_69) | ~r2_hidden(k4_tarski(B_68, C_69), k1_wellord2(A_67)) | ~m1_subset_1(C_69, A_67) | ~m1_subset_1(B_68, A_67))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50, c_50, c_181])).
% 3.33/1.87  tff(c_220, plain, (![A_85, C_86, D_87]: (r1_orders_2(k2_yellow_1(A_85), C_86, D_87) | ~m1_subset_1(D_87, A_85) | ~m1_subset_1(C_86, A_85) | ~r1_tarski(C_86, D_87) | ~r2_hidden(D_87, A_85) | ~r2_hidden(C_86, A_85))), inference(resolution, [status(thm)], [c_74, c_186])).
% 3.33/1.87  tff(c_42, plain, (![A_25]: (v3_orders_2(k2_yellow_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.33/1.87  tff(c_199, plain, (![A_70, B_71, C_72]: (r3_orders_2(A_70, B_71, C_72) | ~r1_orders_2(A_70, B_71, C_72) | ~m1_subset_1(C_72, u1_struct_0(A_70)) | ~m1_subset_1(B_71, u1_struct_0(A_70)) | ~l1_orders_2(A_70) | ~v3_orders_2(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.33/1.87  tff(c_201, plain, (![A_27, B_71, C_72]: (r3_orders_2(k2_yellow_1(A_27), B_71, C_72) | ~r1_orders_2(k2_yellow_1(A_27), B_71, C_72) | ~m1_subset_1(C_72, A_27) | ~m1_subset_1(B_71, u1_struct_0(k2_yellow_1(A_27))) | ~l1_orders_2(k2_yellow_1(A_27)) | ~v3_orders_2(k2_yellow_1(A_27)) | v2_struct_0(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_199])).
% 3.33/1.87  tff(c_204, plain, (![A_73, B_74, C_75]: (r3_orders_2(k2_yellow_1(A_73), B_74, C_75) | ~r1_orders_2(k2_yellow_1(A_73), B_74, C_75) | ~m1_subset_1(C_75, A_73) | ~m1_subset_1(B_74, A_73) | v2_struct_0(k2_yellow_1(A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_50, c_201])).
% 3.33/1.87  tff(c_207, plain, (~r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', '#skF_3') | v2_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_204, c_83])).
% 3.33/1.87  tff(c_210, plain, (~r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | v2_struct_0(k2_yellow_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_68, c_207])).
% 3.33/1.87  tff(c_211, plain, (~r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_210])).
% 3.33/1.87  tff(c_226, plain, (~m1_subset_1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_5') | ~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_220, c_211])).
% 3.33/1.87  tff(c_230, plain, (~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_67, c_68, c_226])).
% 3.33/1.87  tff(c_231, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_230])).
% 3.33/1.87  tff(c_234, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_231])).
% 3.33/1.87  tff(c_237, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_234])).
% 3.33/1.87  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_237])).
% 3.33/1.87  tff(c_240, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_230])).
% 3.33/1.87  tff(c_244, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_240])).
% 3.33/1.87  tff(c_247, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_244])).
% 3.33/1.87  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_247])).
% 3.33/1.87  tff(c_250, plain, (v2_struct_0(k2_yellow_1('#skF_3'))), inference(splitRight, [status(thm)], [c_210])).
% 3.33/1.87  tff(c_121, plain, (![A_43]: (v1_xboole_0(u1_struct_0(A_43)) | ~l1_struct_0(A_43) | ~v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.87  tff(c_124, plain, (![A_27]: (v1_xboole_0(A_27) | ~l1_struct_0(k2_yellow_1(A_27)) | ~v2_struct_0(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_121])).
% 3.33/1.87  tff(c_254, plain, (v1_xboole_0('#skF_3') | ~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_250, c_124])).
% 3.33/1.87  tff(c_257, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_254])).
% 3.33/1.87  tff(c_260, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_257])).
% 3.33/1.87  tff(c_264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_260])).
% 3.33/1.87  tff(c_265, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 3.33/1.87  tff(c_304, plain, (r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_265, c_66])).
% 3.33/1.87  tff(c_385, plain, (![A_126, B_127, C_128]: (r1_orders_2(A_126, B_127, C_128) | ~r3_orders_2(A_126, B_127, C_128) | ~m1_subset_1(C_128, u1_struct_0(A_126)) | ~m1_subset_1(B_127, u1_struct_0(A_126)) | ~l1_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.33/1.87  tff(c_387, plain, (r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(k2_yellow_1('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_3'))) | ~l1_orders_2(k2_yellow_1('#skF_3')) | ~v3_orders_2(k2_yellow_1('#skF_3')) | v2_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_304, c_385])).
% 3.33/1.87  tff(c_390, plain, (r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | v2_struct_0(k2_yellow_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_67, c_50, c_68, c_50, c_387])).
% 3.33/1.87  tff(c_391, plain, (v2_struct_0(k2_yellow_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_390])).
% 3.33/1.87  tff(c_306, plain, (![A_93]: (v1_xboole_0(u1_struct_0(A_93)) | ~l1_struct_0(A_93) | ~v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.87  tff(c_309, plain, (![A_27]: (v1_xboole_0(A_27) | ~l1_struct_0(k2_yellow_1(A_27)) | ~v2_struct_0(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_306])).
% 3.33/1.87  tff(c_394, plain, (v1_xboole_0('#skF_3') | ~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_391, c_309])).
% 3.33/1.87  tff(c_397, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_394])).
% 3.33/1.87  tff(c_400, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_397])).
% 3.33/1.87  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_400])).
% 3.33/1.87  tff(c_405, plain, (r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_390])).
% 3.33/1.87  tff(c_345, plain, (![B_108, C_109, A_110]: (r2_hidden(k4_tarski(B_108, C_109), u1_orders_2(A_110)) | ~r1_orders_2(A_110, B_108, C_109) | ~m1_subset_1(C_109, u1_struct_0(A_110)) | ~m1_subset_1(B_108, u1_struct_0(A_110)) | ~l1_orders_2(A_110))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.33/1.87  tff(c_348, plain, (![B_108, C_109, A_27]: (r2_hidden(k4_tarski(B_108, C_109), k1_wellord2(A_27)) | ~r1_orders_2(k2_yellow_1(A_27), B_108, C_109) | ~m1_subset_1(C_109, u1_struct_0(k2_yellow_1(A_27))) | ~m1_subset_1(B_108, u1_struct_0(k2_yellow_1(A_27))) | ~l1_orders_2(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_345])).
% 3.33/1.87  tff(c_351, plain, (![B_111, C_112, A_113]: (r2_hidden(k4_tarski(B_111, C_112), k1_wellord2(A_113)) | ~r1_orders_2(k2_yellow_1(A_113), B_111, C_112) | ~m1_subset_1(C_112, A_113) | ~m1_subset_1(B_111, A_113))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50, c_50, c_348])).
% 3.33/1.87  tff(c_20, plain, (![C_9, D_10, A_3]: (r1_tarski(C_9, D_10) | ~r2_hidden(k4_tarski(C_9, D_10), k1_wellord2(A_3)) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3) | ~v1_relat_1(k1_wellord2(A_3)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.33/1.87  tff(c_72, plain, (![C_9, D_10, A_3]: (r1_tarski(C_9, D_10) | ~r2_hidden(k4_tarski(C_9, D_10), k1_wellord2(A_3)) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20])).
% 3.33/1.87  tff(c_355, plain, (![B_111, C_112, A_113]: (r1_tarski(B_111, C_112) | ~r2_hidden(C_112, A_113) | ~r2_hidden(B_111, A_113) | ~r1_orders_2(k2_yellow_1(A_113), B_111, C_112) | ~m1_subset_1(C_112, A_113) | ~m1_subset_1(B_111, A_113))), inference(resolution, [status(thm)], [c_351, c_72])).
% 3.33/1.87  tff(c_409, plain, (r1_tarski('#skF_4', '#skF_5') | ~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_405, c_355])).
% 3.33/1.87  tff(c_412, plain, (r1_tarski('#skF_4', '#skF_5') | ~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_68, c_409])).
% 3.33/1.87  tff(c_413, plain, (~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_265, c_412])).
% 3.33/1.87  tff(c_414, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_413])).
% 3.33/1.87  tff(c_417, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_414])).
% 3.33/1.87  tff(c_420, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_417])).
% 3.33/1.87  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_420])).
% 3.33/1.87  tff(c_423, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_413])).
% 3.33/1.87  tff(c_427, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_423])).
% 3.33/1.87  tff(c_430, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_427])).
% 3.33/1.87  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_430])).
% 3.33/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.87  
% 3.33/1.87  Inference rules
% 3.33/1.87  ----------------------
% 3.33/1.87  #Ref     : 0
% 3.33/1.87  #Sup     : 61
% 3.33/1.87  #Fact    : 0
% 3.33/1.87  #Define  : 0
% 3.33/1.87  #Split   : 5
% 3.33/1.87  #Chain   : 0
% 3.33/1.87  #Close   : 0
% 3.33/1.87  
% 3.33/1.87  Ordering : KBO
% 3.33/1.87  
% 3.33/1.87  Simplification rules
% 3.33/1.87  ----------------------
% 3.33/1.87  #Subsume      : 0
% 3.33/1.87  #Demod        : 70
% 3.33/1.87  #Tautology    : 38
% 3.33/1.87  #SimpNegUnit  : 9
% 3.33/1.87  #BackRed      : 0
% 3.33/1.87  
% 3.33/1.87  #Partial instantiations: 0
% 3.33/1.87  #Strategies tried      : 1
% 3.33/1.87  
% 3.33/1.87  Timing (in seconds)
% 3.33/1.87  ----------------------
% 3.33/1.87  Preprocessing        : 0.55
% 3.33/1.87  Parsing              : 0.28
% 3.33/1.87  CNF conversion       : 0.04
% 3.33/1.87  Main loop            : 0.43
% 3.33/1.87  Inferencing          : 0.17
% 3.33/1.87  Reduction            : 0.14
% 3.33/1.87  Demodulation         : 0.10
% 3.33/1.88  BG Simplification    : 0.03
% 3.33/1.88  Subsumption          : 0.06
% 3.33/1.88  Abstraction          : 0.02
% 3.33/1.88  MUC search           : 0.00
% 3.33/1.88  Cooper               : 0.00
% 3.33/1.88  Total                : 1.05
% 3.33/1.88  Index Insertion      : 0.00
% 3.33/1.88  Index Deletion       : 0.00
% 3.33/1.88  Index Matching       : 0.00
% 3.33/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
