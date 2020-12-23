%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:20 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 428 expanded)
%              Number of leaves         :   41 ( 170 expanded)
%              Depth                    :   12
%              Number of atoms          :  231 (1002 expanded)
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

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
               => ( r3_orders_2(k2_yellow_1(A),B,C)
                <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_110,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_55,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_53,axiom,(
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

tff(f_106,axiom,(
    ! [A] : k1_yellow_1(A) = k1_wellord2(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_56,plain,(
    ! [A_27] : u1_struct_0(k2_yellow_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k2_yellow_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_74,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_73,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_62])).

tff(c_44,plain,(
    ! [A_24] : l1_orders_2(k2_yellow_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_72,plain,
    ( r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_89,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_28,plain,(
    ! [A_11] : v1_relat_1(k1_wellord2(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [C_9,D_10,A_3] :
      ( r2_hidden(k4_tarski(C_9,D_10),k1_wellord2(A_3))
      | ~ r1_tarski(C_9,D_10)
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3)
      | ~ v1_relat_1(k1_wellord2(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_80,plain,(
    ! [C_9,D_10,A_3] :
      ( r2_hidden(k4_tarski(C_9,D_10),k1_wellord2(A_3))
      | ~ r1_tarski(C_9,D_10)
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24])).

tff(c_54,plain,(
    ! [A_26] : k1_yellow_1(A_26) = k1_wellord2(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_58,plain,(
    ! [A_27] : u1_orders_2(k2_yellow_1(A_27)) = k1_yellow_1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_75,plain,(
    ! [A_27] : u1_orders_2(k2_yellow_1(A_27)) = k1_wellord2(A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58])).

tff(c_261,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_orders_2(A_75,B_76,C_77)
      | ~ r2_hidden(k4_tarski(B_76,C_77),u1_orders_2(A_75))
      | ~ m1_subset_1(C_77,u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_270,plain,(
    ! [A_27,B_76,C_77] :
      ( r1_orders_2(k2_yellow_1(A_27),B_76,C_77)
      | ~ r2_hidden(k4_tarski(B_76,C_77),k1_wellord2(A_27))
      | ~ m1_subset_1(C_77,u1_struct_0(k2_yellow_1(A_27)))
      | ~ m1_subset_1(B_76,u1_struct_0(k2_yellow_1(A_27)))
      | ~ l1_orders_2(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_261])).

tff(c_275,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_orders_2(k2_yellow_1(A_78),B_79,C_80)
      | ~ r2_hidden(k4_tarski(B_79,C_80),k1_wellord2(A_78))
      | ~ m1_subset_1(C_80,A_78)
      | ~ m1_subset_1(B_79,A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56,c_56,c_270])).

tff(c_321,plain,(
    ! [A_96,C_97,D_98] :
      ( r1_orders_2(k2_yellow_1(A_96),C_97,D_98)
      | ~ m1_subset_1(D_98,A_96)
      | ~ m1_subset_1(C_97,A_96)
      | ~ r1_tarski(C_97,D_98)
      | ~ r2_hidden(D_98,A_96)
      | ~ r2_hidden(C_97,A_96) ) ),
    inference(resolution,[status(thm)],[c_80,c_275])).

tff(c_48,plain,(
    ! [A_25] : v3_orders_2(k2_yellow_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_288,plain,(
    ! [A_81,B_82,C_83] :
      ( r3_orders_2(A_81,B_82,C_83)
      | ~ r1_orders_2(A_81,B_82,C_83)
      | ~ m1_subset_1(C_83,u1_struct_0(A_81))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l1_orders_2(A_81)
      | ~ v3_orders_2(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_293,plain,(
    ! [A_27,B_82,C_83] :
      ( r3_orders_2(k2_yellow_1(A_27),B_82,C_83)
      | ~ r1_orders_2(k2_yellow_1(A_27),B_82,C_83)
      | ~ m1_subset_1(C_83,A_27)
      | ~ m1_subset_1(B_82,u1_struct_0(k2_yellow_1(A_27)))
      | ~ l1_orders_2(k2_yellow_1(A_27))
      | ~ v3_orders_2(k2_yellow_1(A_27))
      | v2_struct_0(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_288])).

tff(c_297,plain,(
    ! [A_84,B_85,C_86] :
      ( r3_orders_2(k2_yellow_1(A_84),B_85,C_86)
      | ~ r1_orders_2(k2_yellow_1(A_84),B_85,C_86)
      | ~ m1_subset_1(C_86,A_84)
      | ~ m1_subset_1(B_85,A_84)
      | v2_struct_0(k2_yellow_1(A_84)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_56,c_293])).

tff(c_66,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_146,plain,(
    ~ r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_66])).

tff(c_300,plain,
    ( ~ r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_297,c_146])).

tff(c_303,plain,
    ( ~ r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_74,c_300])).

tff(c_304,plain,(
    ~ r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_327,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_321,c_304])).

tff(c_331,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_73,c_74,c_327])).

tff(c_332,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_335,plain,
    ( ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_332])).

tff(c_338,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_335])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_338])).

tff(c_341,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_386,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_341])).

tff(c_389,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_386])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_389])).

tff(c_392,plain,(
    v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_128,plain,(
    ! [A_45] :
      ( v1_xboole_0(u1_struct_0(A_45))
      | ~ l1_struct_0(A_45)
      | ~ v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_131,plain,(
    ! [A_27] :
      ( v1_xboole_0(A_27)
      | ~ l1_struct_0(k2_yellow_1(A_27))
      | ~ v2_struct_0(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_128])).

tff(c_396,plain,
    ( v1_xboole_0('#skF_3')
    | ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_392,c_131])).

tff(c_399,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_396])).

tff(c_402,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_399])).

tff(c_406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_402])).

tff(c_408,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_407,plain,(
    r3_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_626,plain,(
    ! [A_152,B_153,C_154] :
      ( r1_orders_2(A_152,B_153,C_154)
      | ~ r3_orders_2(A_152,B_153,C_154)
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l1_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_630,plain,
    ( r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0(k2_yellow_1('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_3')))
    | ~ l1_orders_2(k2_yellow_1('#skF_3'))
    | ~ v3_orders_2(k2_yellow_1('#skF_3'))
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_407,c_626])).

tff(c_636,plain,
    ( r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5')
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_73,c_56,c_74,c_56,c_630])).

tff(c_637,plain,(
    v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_636])).

tff(c_462,plain,(
    ! [A_109] :
      ( v1_xboole_0(u1_struct_0(A_109))
      | ~ l1_struct_0(A_109)
      | ~ v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_465,plain,(
    ! [A_27] :
      ( v1_xboole_0(A_27)
      | ~ l1_struct_0(k2_yellow_1(A_27))
      | ~ v2_struct_0(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_462])).

tff(c_640,plain,
    ( v1_xboole_0('#skF_3')
    | ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_637,c_465])).

tff(c_643,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_640])).

tff(c_646,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_643])).

tff(c_650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_646])).

tff(c_651,plain,(
    r1_orders_2(k2_yellow_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_636])).

tff(c_580,plain,(
    ! [B_137,C_138,A_139] :
      ( r2_hidden(k4_tarski(B_137,C_138),u1_orders_2(A_139))
      | ~ r1_orders_2(A_139,B_137,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(A_139))
      | ~ m1_subset_1(B_137,u1_struct_0(A_139))
      | ~ l1_orders_2(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_589,plain,(
    ! [B_137,C_138,A_27] :
      ( r2_hidden(k4_tarski(B_137,C_138),k1_wellord2(A_27))
      | ~ r1_orders_2(k2_yellow_1(A_27),B_137,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(k2_yellow_1(A_27)))
      | ~ m1_subset_1(B_137,u1_struct_0(k2_yellow_1(A_27)))
      | ~ l1_orders_2(k2_yellow_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_580])).

tff(c_603,plain,(
    ! [B_143,C_144,A_145] :
      ( r2_hidden(k4_tarski(B_143,C_144),k1_wellord2(A_145))
      | ~ r1_orders_2(k2_yellow_1(A_145),B_143,C_144)
      | ~ m1_subset_1(C_144,A_145)
      | ~ m1_subset_1(B_143,A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56,c_56,c_589])).

tff(c_26,plain,(
    ! [C_9,D_10,A_3] :
      ( r1_tarski(C_9,D_10)
      | ~ r2_hidden(k4_tarski(C_9,D_10),k1_wellord2(A_3))
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3)
      | ~ v1_relat_1(k1_wellord2(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    ! [C_9,D_10,A_3] :
      ( r1_tarski(C_9,D_10)
      | ~ r2_hidden(k4_tarski(C_9,D_10),k1_wellord2(A_3))
      | ~ r2_hidden(D_10,A_3)
      | ~ r2_hidden(C_9,A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_688,plain,(
    ! [B_159,C_160,A_161] :
      ( r1_tarski(B_159,C_160)
      | ~ r2_hidden(C_160,A_161)
      | ~ r2_hidden(B_159,A_161)
      | ~ r1_orders_2(k2_yellow_1(A_161),B_159,C_160)
      | ~ m1_subset_1(C_160,A_161)
      | ~ m1_subset_1(B_159,A_161) ) ),
    inference(resolution,[status(thm)],[c_603,c_78])).

tff(c_694,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_651,c_688])).

tff(c_698,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_74,c_694])).

tff(c_699,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_698])).

tff(c_700,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_699])).

tff(c_703,plain,
    ( ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_700])).

tff(c_706,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_703])).

tff(c_708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_706])).

tff(c_709,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_699])).

tff(c_713,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_709])).

tff(c_716,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_713])).

tff(c_718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.45  
% 2.90/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.45  %$ r3_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k4_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_relat_1 > k2_yellow_1 > k1_yellow_1 > k1_wellord2 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.90/1.45  
% 2.90/1.45  %Foreground sorts:
% 2.90/1.45  
% 2.90/1.45  
% 2.90/1.45  %Background operators:
% 2.90/1.45  
% 2.90/1.45  
% 2.90/1.45  %Foreground operators:
% 2.90/1.45  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.90/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.90/1.45  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.90/1.45  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.90/1.45  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.90/1.45  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.90/1.45  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.90/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.90/1.45  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.90/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.90/1.45  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.90/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.90/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.45  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.90/1.45  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.90/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.45  
% 3.04/1.47  tff(f_124, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.04/1.47  tff(f_110, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.04/1.47  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.04/1.47  tff(f_96, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.04/1.47  tff(f_77, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.04/1.47  tff(f_55, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.04/1.47  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 3.04/1.47  tff(f_106, axiom, (![A]: (k1_yellow_1(A) = k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_yellow_1)).
% 3.04/1.47  tff(f_73, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 3.04/1.47  tff(f_104, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.04/1.47  tff(f_92, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.04/1.47  tff(f_61, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_struct_0)).
% 3.04/1.47  tff(c_64, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.04/1.47  tff(c_56, plain, (![A_27]: (u1_struct_0(k2_yellow_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.04/1.47  tff(c_60, plain, (m1_subset_1('#skF_5', u1_struct_0(k2_yellow_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.04/1.47  tff(c_74, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60])).
% 3.04/1.47  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.04/1.47  tff(c_62, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.04/1.47  tff(c_73, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_62])).
% 3.04/1.47  tff(c_44, plain, (![A_24]: (l1_orders_2(k2_yellow_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.04/1.47  tff(c_36, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.04/1.47  tff(c_72, plain, (r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.04/1.47  tff(c_89, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 3.04/1.47  tff(c_28, plain, (![A_11]: (v1_relat_1(k1_wellord2(A_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.04/1.47  tff(c_24, plain, (![C_9, D_10, A_3]: (r2_hidden(k4_tarski(C_9, D_10), k1_wellord2(A_3)) | ~r1_tarski(C_9, D_10) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3) | ~v1_relat_1(k1_wellord2(A_3)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.04/1.47  tff(c_80, plain, (![C_9, D_10, A_3]: (r2_hidden(k4_tarski(C_9, D_10), k1_wellord2(A_3)) | ~r1_tarski(C_9, D_10) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24])).
% 3.04/1.47  tff(c_54, plain, (![A_26]: (k1_yellow_1(A_26)=k1_wellord2(A_26))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.04/1.47  tff(c_58, plain, (![A_27]: (u1_orders_2(k2_yellow_1(A_27))=k1_yellow_1(A_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.04/1.47  tff(c_75, plain, (![A_27]: (u1_orders_2(k2_yellow_1(A_27))=k1_wellord2(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58])).
% 3.04/1.47  tff(c_261, plain, (![A_75, B_76, C_77]: (r1_orders_2(A_75, B_76, C_77) | ~r2_hidden(k4_tarski(B_76, C_77), u1_orders_2(A_75)) | ~m1_subset_1(C_77, u1_struct_0(A_75)) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_orders_2(A_75))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.04/1.47  tff(c_270, plain, (![A_27, B_76, C_77]: (r1_orders_2(k2_yellow_1(A_27), B_76, C_77) | ~r2_hidden(k4_tarski(B_76, C_77), k1_wellord2(A_27)) | ~m1_subset_1(C_77, u1_struct_0(k2_yellow_1(A_27))) | ~m1_subset_1(B_76, u1_struct_0(k2_yellow_1(A_27))) | ~l1_orders_2(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_261])).
% 3.04/1.47  tff(c_275, plain, (![A_78, B_79, C_80]: (r1_orders_2(k2_yellow_1(A_78), B_79, C_80) | ~r2_hidden(k4_tarski(B_79, C_80), k1_wellord2(A_78)) | ~m1_subset_1(C_80, A_78) | ~m1_subset_1(B_79, A_78))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56, c_56, c_270])).
% 3.04/1.47  tff(c_321, plain, (![A_96, C_97, D_98]: (r1_orders_2(k2_yellow_1(A_96), C_97, D_98) | ~m1_subset_1(D_98, A_96) | ~m1_subset_1(C_97, A_96) | ~r1_tarski(C_97, D_98) | ~r2_hidden(D_98, A_96) | ~r2_hidden(C_97, A_96))), inference(resolution, [status(thm)], [c_80, c_275])).
% 3.04/1.47  tff(c_48, plain, (![A_25]: (v3_orders_2(k2_yellow_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.04/1.47  tff(c_288, plain, (![A_81, B_82, C_83]: (r3_orders_2(A_81, B_82, C_83) | ~r1_orders_2(A_81, B_82, C_83) | ~m1_subset_1(C_83, u1_struct_0(A_81)) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l1_orders_2(A_81) | ~v3_orders_2(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.04/1.47  tff(c_293, plain, (![A_27, B_82, C_83]: (r3_orders_2(k2_yellow_1(A_27), B_82, C_83) | ~r1_orders_2(k2_yellow_1(A_27), B_82, C_83) | ~m1_subset_1(C_83, A_27) | ~m1_subset_1(B_82, u1_struct_0(k2_yellow_1(A_27))) | ~l1_orders_2(k2_yellow_1(A_27)) | ~v3_orders_2(k2_yellow_1(A_27)) | v2_struct_0(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_288])).
% 3.04/1.47  tff(c_297, plain, (![A_84, B_85, C_86]: (r3_orders_2(k2_yellow_1(A_84), B_85, C_86) | ~r1_orders_2(k2_yellow_1(A_84), B_85, C_86) | ~m1_subset_1(C_86, A_84) | ~m1_subset_1(B_85, A_84) | v2_struct_0(k2_yellow_1(A_84)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_56, c_293])).
% 3.04/1.47  tff(c_66, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.04/1.47  tff(c_146, plain, (~r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_66])).
% 3.04/1.47  tff(c_300, plain, (~r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', '#skF_3') | v2_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_297, c_146])).
% 3.04/1.47  tff(c_303, plain, (~r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | v2_struct_0(k2_yellow_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_74, c_300])).
% 3.04/1.47  tff(c_304, plain, (~r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_303])).
% 3.04/1.47  tff(c_327, plain, (~m1_subset_1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_5') | ~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_321, c_304])).
% 3.04/1.47  tff(c_331, plain, (~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_73, c_74, c_327])).
% 3.04/1.47  tff(c_332, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_331])).
% 3.04/1.47  tff(c_335, plain, (~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_332])).
% 3.04/1.47  tff(c_338, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_335])).
% 3.04/1.47  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_338])).
% 3.04/1.47  tff(c_341, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_331])).
% 3.04/1.47  tff(c_386, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_341])).
% 3.04/1.47  tff(c_389, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_386])).
% 3.04/1.47  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_389])).
% 3.04/1.47  tff(c_392, plain, (v2_struct_0(k2_yellow_1('#skF_3'))), inference(splitRight, [status(thm)], [c_303])).
% 3.04/1.47  tff(c_128, plain, (![A_45]: (v1_xboole_0(u1_struct_0(A_45)) | ~l1_struct_0(A_45) | ~v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.04/1.47  tff(c_131, plain, (![A_27]: (v1_xboole_0(A_27) | ~l1_struct_0(k2_yellow_1(A_27)) | ~v2_struct_0(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_128])).
% 3.04/1.47  tff(c_396, plain, (v1_xboole_0('#skF_3') | ~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_392, c_131])).
% 3.04/1.47  tff(c_399, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_396])).
% 3.04/1.47  tff(c_402, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_399])).
% 3.04/1.47  tff(c_406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_402])).
% 3.04/1.47  tff(c_408, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 3.04/1.47  tff(c_407, plain, (r3_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 3.04/1.47  tff(c_626, plain, (![A_152, B_153, C_154]: (r1_orders_2(A_152, B_153, C_154) | ~r3_orders_2(A_152, B_153, C_154) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l1_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.04/1.47  tff(c_630, plain, (r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(k2_yellow_1('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_3'))) | ~l1_orders_2(k2_yellow_1('#skF_3')) | ~v3_orders_2(k2_yellow_1('#skF_3')) | v2_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_407, c_626])).
% 3.04/1.47  tff(c_636, plain, (r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5') | v2_struct_0(k2_yellow_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_73, c_56, c_74, c_56, c_630])).
% 3.04/1.47  tff(c_637, plain, (v2_struct_0(k2_yellow_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_636])).
% 3.04/1.47  tff(c_462, plain, (![A_109]: (v1_xboole_0(u1_struct_0(A_109)) | ~l1_struct_0(A_109) | ~v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.04/1.47  tff(c_465, plain, (![A_27]: (v1_xboole_0(A_27) | ~l1_struct_0(k2_yellow_1(A_27)) | ~v2_struct_0(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_462])).
% 3.04/1.47  tff(c_640, plain, (v1_xboole_0('#skF_3') | ~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_637, c_465])).
% 3.04/1.47  tff(c_643, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_640])).
% 3.04/1.47  tff(c_646, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_643])).
% 3.04/1.47  tff(c_650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_646])).
% 3.04/1.47  tff(c_651, plain, (r1_orders_2(k2_yellow_1('#skF_3'), '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_636])).
% 3.04/1.47  tff(c_580, plain, (![B_137, C_138, A_139]: (r2_hidden(k4_tarski(B_137, C_138), u1_orders_2(A_139)) | ~r1_orders_2(A_139, B_137, C_138) | ~m1_subset_1(C_138, u1_struct_0(A_139)) | ~m1_subset_1(B_137, u1_struct_0(A_139)) | ~l1_orders_2(A_139))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.04/1.47  tff(c_589, plain, (![B_137, C_138, A_27]: (r2_hidden(k4_tarski(B_137, C_138), k1_wellord2(A_27)) | ~r1_orders_2(k2_yellow_1(A_27), B_137, C_138) | ~m1_subset_1(C_138, u1_struct_0(k2_yellow_1(A_27))) | ~m1_subset_1(B_137, u1_struct_0(k2_yellow_1(A_27))) | ~l1_orders_2(k2_yellow_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_580])).
% 3.04/1.47  tff(c_603, plain, (![B_143, C_144, A_145]: (r2_hidden(k4_tarski(B_143, C_144), k1_wellord2(A_145)) | ~r1_orders_2(k2_yellow_1(A_145), B_143, C_144) | ~m1_subset_1(C_144, A_145) | ~m1_subset_1(B_143, A_145))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56, c_56, c_589])).
% 3.04/1.47  tff(c_26, plain, (![C_9, D_10, A_3]: (r1_tarski(C_9, D_10) | ~r2_hidden(k4_tarski(C_9, D_10), k1_wellord2(A_3)) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3) | ~v1_relat_1(k1_wellord2(A_3)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.04/1.47  tff(c_78, plain, (![C_9, D_10, A_3]: (r1_tarski(C_9, D_10) | ~r2_hidden(k4_tarski(C_9, D_10), k1_wellord2(A_3)) | ~r2_hidden(D_10, A_3) | ~r2_hidden(C_9, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 3.04/1.47  tff(c_688, plain, (![B_159, C_160, A_161]: (r1_tarski(B_159, C_160) | ~r2_hidden(C_160, A_161) | ~r2_hidden(B_159, A_161) | ~r1_orders_2(k2_yellow_1(A_161), B_159, C_160) | ~m1_subset_1(C_160, A_161) | ~m1_subset_1(B_159, A_161))), inference(resolution, [status(thm)], [c_603, c_78])).
% 3.04/1.47  tff(c_694, plain, (r1_tarski('#skF_4', '#skF_5') | ~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3') | ~m1_subset_1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_651, c_688])).
% 3.04/1.47  tff(c_698, plain, (r1_tarski('#skF_4', '#skF_5') | ~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_74, c_694])).
% 3.04/1.47  tff(c_699, plain, (~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_408, c_698])).
% 3.04/1.47  tff(c_700, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_699])).
% 3.04/1.47  tff(c_703, plain, (~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_700])).
% 3.04/1.47  tff(c_706, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_703])).
% 3.04/1.47  tff(c_708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_706])).
% 3.04/1.47  tff(c_709, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_699])).
% 3.04/1.47  tff(c_713, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_709])).
% 3.04/1.47  tff(c_716, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_713])).
% 3.04/1.47  tff(c_718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_716])).
% 3.04/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.47  
% 3.04/1.47  Inference rules
% 3.04/1.47  ----------------------
% 3.04/1.47  #Ref     : 0
% 3.04/1.47  #Sup     : 119
% 3.04/1.47  #Fact    : 0
% 3.04/1.47  #Define  : 0
% 3.04/1.47  #Split   : 5
% 3.04/1.47  #Chain   : 0
% 3.04/1.47  #Close   : 0
% 3.04/1.47  
% 3.04/1.47  Ordering : KBO
% 3.04/1.47  
% 3.04/1.47  Simplification rules
% 3.04/1.47  ----------------------
% 3.04/1.47  #Subsume      : 5
% 3.04/1.47  #Demod        : 159
% 3.04/1.47  #Tautology    : 72
% 3.04/1.47  #SimpNegUnit  : 8
% 3.04/1.47  #BackRed      : 0
% 3.04/1.47  
% 3.04/1.47  #Partial instantiations: 0
% 3.04/1.47  #Strategies tried      : 1
% 3.04/1.47  
% 3.04/1.47  Timing (in seconds)
% 3.04/1.47  ----------------------
% 3.04/1.48  Preprocessing        : 0.33
% 3.04/1.48  Parsing              : 0.17
% 3.04/1.48  CNF conversion       : 0.03
% 3.04/1.48  Main loop            : 0.33
% 3.04/1.48  Inferencing          : 0.13
% 3.04/1.48  Reduction            : 0.11
% 3.04/1.48  Demodulation         : 0.08
% 3.04/1.48  BG Simplification    : 0.02
% 3.04/1.48  Subsumption          : 0.05
% 3.04/1.48  Abstraction          : 0.02
% 3.04/1.48  MUC search           : 0.00
% 3.04/1.48  Cooper               : 0.00
% 3.04/1.48  Total                : 0.70
% 3.04/1.48  Index Insertion      : 0.00
% 3.04/1.48  Index Deletion       : 0.00
% 3.04/1.48  Index Matching       : 0.00
% 3.04/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
