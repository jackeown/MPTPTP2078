%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:55 EST 2020

% Result     : Theorem 5.87s
% Output     : CNFRefutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 180 expanded)
%              Number of leaves         :   40 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  183 ( 360 expanded)
%              Number of equality atoms :   45 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_60,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3060,plain,(
    ! [B_351,A_352] :
      ( r1_tarski(B_351,k2_pre_topc(A_352,B_351))
      | ~ m1_subset_1(B_351,k1_zfmisc_1(u1_struct_0(A_352)))
      | ~ l1_pre_topc(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3062,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_3060])).

tff(c_3065,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3062])).

tff(c_75,plain,(
    ! [B_51,A_52] : k2_xboole_0(B_51,A_52) = k2_xboole_0(A_52,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_91,plain,(
    ! [A_52] : k2_xboole_0(k1_xboole_0,A_52) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_22])).

tff(c_2862,plain,(
    ! [A_309,B_310] : k2_xboole_0(A_309,k4_xboole_0(B_310,A_309)) = k2_xboole_0(A_309,B_310) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2869,plain,(
    ! [B_310] : k4_xboole_0(B_310,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_310) ),
    inference(superposition,[status(thm),theory(equality)],[c_2862,c_91])).

tff(c_2878,plain,(
    ! [B_310] : k4_xboole_0(B_310,k1_xboole_0) = B_310 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_2869])).

tff(c_3330,plain,(
    ! [A_393,B_394] :
      ( m1_subset_1(k2_pre_topc(A_393,B_394),k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ m1_subset_1(B_394,k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ l1_pre_topc(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    ! [A_27,B_28,C_29] :
      ( k7_subset_1(A_27,B_28,C_29) = k4_xboole_0(B_28,C_29)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4934,plain,(
    ! [A_584,B_585,C_586] :
      ( k7_subset_1(u1_struct_0(A_584),k2_pre_topc(A_584,B_585),C_586) = k4_xboole_0(k2_pre_topc(A_584,B_585),C_586)
      | ~ m1_subset_1(B_585,k1_zfmisc_1(u1_struct_0(A_584)))
      | ~ l1_pre_topc(A_584) ) ),
    inference(resolution,[status(thm)],[c_3330,c_36])).

tff(c_4938,plain,(
    ! [C_586] :
      ( k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),C_586) = k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),C_586)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_4934])).

tff(c_4960,plain,(
    ! [C_588] : k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),C_588) = k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),C_588) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4938])).

tff(c_56,plain,
    ( ~ r1_tarski('#skF_4',k2_tops_1('#skF_3','#skF_4'))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_161,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_993,plain,(
    ! [B_175,A_176] :
      ( v2_tops_1(B_175,A_176)
      | k1_tops_1(A_176,B_175) != k1_xboole_0
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_996,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_993])).

tff(c_999,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_996])).

tff(c_1000,plain,(
    k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_999])).

tff(c_20,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_579,plain,(
    ! [A_132,B_133] :
      ( r1_tarski(k1_tops_1(A_132,B_133),B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_581,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_579])).

tff(c_584,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_581])).

tff(c_62,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | r1_tarski('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_215,plain,(
    r1_tarski('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_62])).

tff(c_333,plain,(
    ! [A_88,C_89,B_90] :
      ( r1_tarski(A_88,C_89)
      | ~ r1_tarski(B_90,C_89)
      | ~ r1_tarski(A_88,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_354,plain,(
    ! [A_93] :
      ( r1_tarski(A_93,k2_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski(A_93,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_215,c_333])).

tff(c_24,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(A_16,C_18)
      | ~ r1_tarski(B_17,C_18)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_359,plain,(
    ! [A_16,A_93] :
      ( r1_tarski(A_16,k2_tops_1('#skF_3','#skF_4'))
      | ~ r1_tarski(A_16,A_93)
      | ~ r1_tarski(A_93,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_354,c_24])).

tff(c_586,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),k2_tops_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_584,c_359])).

tff(c_593,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),k2_tops_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_586])).

tff(c_781,plain,(
    ! [A_152,B_153] :
      ( r1_xboole_0(k1_tops_1(A_152,B_153),k2_tops_1(A_152,B_153))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2005,plain,(
    ! [A_262,B_263] :
      ( k4_xboole_0(k1_tops_1(A_262,B_263),k2_tops_1(A_262,B_263)) = k1_tops_1(A_262,B_263)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262) ) ),
    inference(resolution,[status(thm)],[c_781,c_30])).

tff(c_2009,plain,
    ( k4_xboole_0(k1_tops_1('#skF_3','#skF_4'),k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2005])).

tff(c_2013,plain,(
    k4_xboole_0(k1_tops_1('#skF_3','#skF_4'),k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2009])).

tff(c_169,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_xboole_0(A_58,k4_xboole_0(C_59,B_60))
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_173,plain,(
    ! [A_58,C_59,B_60] :
      ( k4_xboole_0(A_58,k4_xboole_0(C_59,B_60)) = A_58
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(resolution,[status(thm)],[c_169,c_30])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_305,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,B_84)
      | ~ r2_hidden(C_85,A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_460,plain,(
    ! [C_110,B_111,A_112] :
      ( ~ r2_hidden(C_110,B_111)
      | ~ r2_hidden(C_110,A_112)
      | k4_xboole_0(A_112,B_111) != A_112 ) ),
    inference(resolution,[status(thm)],[c_32,c_305])).

tff(c_1728,plain,(
    ! [A_240,B_241,A_242] :
      ( ~ r2_hidden('#skF_2'(A_240,B_241),A_242)
      | k4_xboole_0(A_242,B_241) != A_242
      | r1_xboole_0(A_240,B_241) ) ),
    inference(resolution,[status(thm)],[c_12,c_460])).

tff(c_1745,plain,(
    ! [B_243,A_244] :
      ( k4_xboole_0(B_243,B_243) != B_243
      | r1_xboole_0(A_244,B_243) ) ),
    inference(resolution,[status(thm)],[c_12,c_1728])).

tff(c_1759,plain,(
    ! [A_244,C_59,B_60] :
      ( r1_xboole_0(A_244,k4_xboole_0(C_59,B_60))
      | ~ r1_tarski(k4_xboole_0(C_59,B_60),B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_1745])).

tff(c_2018,plain,(
    ! [A_244] :
      ( r1_xboole_0(A_244,k4_xboole_0(k1_tops_1('#skF_3','#skF_4'),k2_tops_1('#skF_3','#skF_4')))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),k2_tops_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2013,c_1759])).

tff(c_2095,plain,(
    ! [A_264] : r1_xboole_0(A_264,k1_tops_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_2013,c_2018])).

tff(c_2102,plain,(
    ! [A_264] : k4_xboole_0(A_264,k1_tops_1('#skF_3','#skF_4')) = A_264 ),
    inference(resolution,[status(thm)],[c_2095,c_30])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2683,plain,(
    ! [A_297,B_298,A_299] :
      ( ~ r2_hidden('#skF_1'(A_297,B_298),A_299)
      | k4_xboole_0(A_299,A_297) != A_299
      | r1_tarski(A_297,B_298) ) ),
    inference(resolution,[status(thm)],[c_8,c_460])).

tff(c_2692,plain,(
    ! [A_300,B_301] :
      ( k4_xboole_0(A_300,A_300) != A_300
      | r1_tarski(A_300,B_301) ) ),
    inference(resolution,[status(thm)],[c_8,c_2683])).

tff(c_2721,plain,(
    ! [B_302] : r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_302) ),
    inference(superposition,[status(thm),theory(equality)],[c_2102,c_2692])).

tff(c_26,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_272,plain,(
    ! [B_78,A_79] :
      ( B_78 = A_79
      | ~ r1_tarski(B_78,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_284,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_272])).

tff(c_2791,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2721,c_284])).

tff(c_2841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1000,c_2791])).

tff(c_2843,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3194,plain,(
    ! [A_370,B_371] :
      ( k1_tops_1(A_370,B_371) = k1_xboole_0
      | ~ v2_tops_1(B_371,A_370)
      | ~ m1_subset_1(B_371,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ l1_pre_topc(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3197,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_3194])).

tff(c_3200,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2843,c_3197])).

tff(c_3788,plain,(
    ! [A_452,B_453] :
      ( k7_subset_1(u1_struct_0(A_452),k2_pre_topc(A_452,B_453),k1_tops_1(A_452,B_453)) = k2_tops_1(A_452,B_453)
      | ~ m1_subset_1(B_453,k1_zfmisc_1(u1_struct_0(A_452)))
      | ~ l1_pre_topc(A_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3797,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),k1_xboole_0) = k2_tops_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3200,c_3788])).

tff(c_3801,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3','#skF_4'),k1_xboole_0) = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3797])).

tff(c_4966,plain,(
    k4_xboole_0(k2_pre_topc('#skF_3','#skF_4'),k1_xboole_0) = k2_tops_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4960,c_3801])).

tff(c_4982,plain,(
    k2_tops_1('#skF_3','#skF_4') = k2_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2878,c_4966])).

tff(c_2842,plain,(
    ~ r1_tarski('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4990,plain,(
    ~ r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4982,c_2842])).

tff(c_4993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3065,c_4990])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:48:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.87/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.23  
% 5.87/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.24  %$ v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.87/2.24  
% 5.87/2.24  %Foreground sorts:
% 5.87/2.24  
% 5.87/2.24  
% 5.87/2.24  %Background operators:
% 5.87/2.24  
% 5.87/2.24  
% 5.87/2.24  %Foreground operators:
% 5.87/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.87/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.87/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.87/2.24  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.87/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.87/2.24  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 5.87/2.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.87/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.87/2.24  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.87/2.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.87/2.24  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.87/2.24  tff('#skF_3', type, '#skF_3': $i).
% 5.87/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.87/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.87/2.24  tff('#skF_4', type, '#skF_4': $i).
% 5.87/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.87/2.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.87/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.87/2.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.87/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.87/2.24  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.87/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.87/2.24  
% 5.87/2.26  tff(f_135, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 5.87/2.26  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 5.87/2.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.87/2.26  tff(f_60, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.87/2.26  tff(f_70, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.87/2.26  tff(f_88, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 5.87/2.26  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.87/2.26  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 5.87/2.26  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.87/2.26  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 5.87/2.26  tff(f_66, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.87/2.26  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tops_1)).
% 5.87/2.26  tff(f_74, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.87/2.26  tff(f_78, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.87/2.26  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.87/2.26  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.87/2.26  tff(f_68, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.87/2.26  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.87/2.26  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.87/2.26  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.87/2.26  tff(c_3060, plain, (![B_351, A_352]: (r1_tarski(B_351, k2_pre_topc(A_352, B_351)) | ~m1_subset_1(B_351, k1_zfmisc_1(u1_struct_0(A_352))) | ~l1_pre_topc(A_352))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.87/2.26  tff(c_3062, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_3060])).
% 5.87/2.26  tff(c_3065, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3062])).
% 5.87/2.26  tff(c_75, plain, (![B_51, A_52]: (k2_xboole_0(B_51, A_52)=k2_xboole_0(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.87/2.26  tff(c_22, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.87/2.26  tff(c_91, plain, (![A_52]: (k2_xboole_0(k1_xboole_0, A_52)=A_52)), inference(superposition, [status(thm), theory('equality')], [c_75, c_22])).
% 5.87/2.26  tff(c_2862, plain, (![A_309, B_310]: (k2_xboole_0(A_309, k4_xboole_0(B_310, A_309))=k2_xboole_0(A_309, B_310))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.87/2.26  tff(c_2869, plain, (![B_310]: (k4_xboole_0(B_310, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_310))), inference(superposition, [status(thm), theory('equality')], [c_2862, c_91])).
% 5.87/2.26  tff(c_2878, plain, (![B_310]: (k4_xboole_0(B_310, k1_xboole_0)=B_310)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_2869])).
% 5.87/2.26  tff(c_3330, plain, (![A_393, B_394]: (m1_subset_1(k2_pre_topc(A_393, B_394), k1_zfmisc_1(u1_struct_0(A_393))) | ~m1_subset_1(B_394, k1_zfmisc_1(u1_struct_0(A_393))) | ~l1_pre_topc(A_393))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.87/2.26  tff(c_36, plain, (![A_27, B_28, C_29]: (k7_subset_1(A_27, B_28, C_29)=k4_xboole_0(B_28, C_29) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.87/2.26  tff(c_4934, plain, (![A_584, B_585, C_586]: (k7_subset_1(u1_struct_0(A_584), k2_pre_topc(A_584, B_585), C_586)=k4_xboole_0(k2_pre_topc(A_584, B_585), C_586) | ~m1_subset_1(B_585, k1_zfmisc_1(u1_struct_0(A_584))) | ~l1_pre_topc(A_584))), inference(resolution, [status(thm)], [c_3330, c_36])).
% 5.87/2.26  tff(c_4938, plain, (![C_586]: (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), C_586)=k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), C_586) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_4934])).
% 5.87/2.26  tff(c_4960, plain, (![C_588]: (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), C_588)=k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), C_588))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4938])).
% 5.87/2.26  tff(c_56, plain, (~r1_tarski('#skF_4', k2_tops_1('#skF_3', '#skF_4')) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.87/2.26  tff(c_161, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 5.87/2.26  tff(c_993, plain, (![B_175, A_176]: (v2_tops_1(B_175, A_176) | k1_tops_1(A_176, B_175)!=k1_xboole_0 | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.87/2.26  tff(c_996, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_993])).
% 5.87/2.26  tff(c_999, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_996])).
% 5.87/2.26  tff(c_1000, plain, (k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_161, c_999])).
% 5.87/2.26  tff(c_20, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.87/2.26  tff(c_579, plain, (![A_132, B_133]: (r1_tarski(k1_tops_1(A_132, B_133), B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.87/2.26  tff(c_581, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_579])).
% 5.87/2.26  tff(c_584, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_581])).
% 5.87/2.26  tff(c_62, plain, (v2_tops_1('#skF_4', '#skF_3') | r1_tarski('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.87/2.26  tff(c_215, plain, (r1_tarski('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_161, c_62])).
% 5.87/2.26  tff(c_333, plain, (![A_88, C_89, B_90]: (r1_tarski(A_88, C_89) | ~r1_tarski(B_90, C_89) | ~r1_tarski(A_88, B_90))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.87/2.26  tff(c_354, plain, (![A_93]: (r1_tarski(A_93, k2_tops_1('#skF_3', '#skF_4')) | ~r1_tarski(A_93, '#skF_4'))), inference(resolution, [status(thm)], [c_215, c_333])).
% 5.87/2.26  tff(c_24, plain, (![A_16, C_18, B_17]: (r1_tarski(A_16, C_18) | ~r1_tarski(B_17, C_18) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.87/2.26  tff(c_359, plain, (![A_16, A_93]: (r1_tarski(A_16, k2_tops_1('#skF_3', '#skF_4')) | ~r1_tarski(A_16, A_93) | ~r1_tarski(A_93, '#skF_4'))), inference(resolution, [status(thm)], [c_354, c_24])).
% 5.87/2.26  tff(c_586, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), k2_tops_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_584, c_359])).
% 5.87/2.26  tff(c_593, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), k2_tops_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_586])).
% 5.87/2.26  tff(c_781, plain, (![A_152, B_153]: (r1_xboole_0(k1_tops_1(A_152, B_153), k2_tops_1(A_152, B_153)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.87/2.26  tff(c_30, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.87/2.26  tff(c_2005, plain, (![A_262, B_263]: (k4_xboole_0(k1_tops_1(A_262, B_263), k2_tops_1(A_262, B_263))=k1_tops_1(A_262, B_263) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262))), inference(resolution, [status(thm)], [c_781, c_30])).
% 5.87/2.26  tff(c_2009, plain, (k4_xboole_0(k1_tops_1('#skF_3', '#skF_4'), k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2005])).
% 5.87/2.26  tff(c_2013, plain, (k4_xboole_0(k1_tops_1('#skF_3', '#skF_4'), k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2009])).
% 5.87/2.26  tff(c_169, plain, (![A_58, C_59, B_60]: (r1_xboole_0(A_58, k4_xboole_0(C_59, B_60)) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.87/2.26  tff(c_173, plain, (![A_58, C_59, B_60]: (k4_xboole_0(A_58, k4_xboole_0(C_59, B_60))=A_58 | ~r1_tarski(A_58, B_60))), inference(resolution, [status(thm)], [c_169, c_30])).
% 5.87/2.26  tff(c_12, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.87/2.26  tff(c_32, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k4_xboole_0(A_22, B_23)!=A_22)), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.87/2.26  tff(c_305, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, B_84) | ~r2_hidden(C_85, A_83))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.87/2.26  tff(c_460, plain, (![C_110, B_111, A_112]: (~r2_hidden(C_110, B_111) | ~r2_hidden(C_110, A_112) | k4_xboole_0(A_112, B_111)!=A_112)), inference(resolution, [status(thm)], [c_32, c_305])).
% 5.87/2.26  tff(c_1728, plain, (![A_240, B_241, A_242]: (~r2_hidden('#skF_2'(A_240, B_241), A_242) | k4_xboole_0(A_242, B_241)!=A_242 | r1_xboole_0(A_240, B_241))), inference(resolution, [status(thm)], [c_12, c_460])).
% 5.87/2.26  tff(c_1745, plain, (![B_243, A_244]: (k4_xboole_0(B_243, B_243)!=B_243 | r1_xboole_0(A_244, B_243))), inference(resolution, [status(thm)], [c_12, c_1728])).
% 5.87/2.26  tff(c_1759, plain, (![A_244, C_59, B_60]: (r1_xboole_0(A_244, k4_xboole_0(C_59, B_60)) | ~r1_tarski(k4_xboole_0(C_59, B_60), B_60))), inference(superposition, [status(thm), theory('equality')], [c_173, c_1745])).
% 5.87/2.26  tff(c_2018, plain, (![A_244]: (r1_xboole_0(A_244, k4_xboole_0(k1_tops_1('#skF_3', '#skF_4'), k2_tops_1('#skF_3', '#skF_4'))) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), k2_tops_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2013, c_1759])).
% 5.87/2.26  tff(c_2095, plain, (![A_264]: (r1_xboole_0(A_264, k1_tops_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_2013, c_2018])).
% 5.87/2.26  tff(c_2102, plain, (![A_264]: (k4_xboole_0(A_264, k1_tops_1('#skF_3', '#skF_4'))=A_264)), inference(resolution, [status(thm)], [c_2095, c_30])).
% 5.87/2.26  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.87/2.26  tff(c_2683, plain, (![A_297, B_298, A_299]: (~r2_hidden('#skF_1'(A_297, B_298), A_299) | k4_xboole_0(A_299, A_297)!=A_299 | r1_tarski(A_297, B_298))), inference(resolution, [status(thm)], [c_8, c_460])).
% 5.87/2.26  tff(c_2692, plain, (![A_300, B_301]: (k4_xboole_0(A_300, A_300)!=A_300 | r1_tarski(A_300, B_301))), inference(resolution, [status(thm)], [c_8, c_2683])).
% 5.87/2.26  tff(c_2721, plain, (![B_302]: (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_302))), inference(superposition, [status(thm), theory('equality')], [c_2102, c_2692])).
% 5.87/2.26  tff(c_26, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.87/2.26  tff(c_272, plain, (![B_78, A_79]: (B_78=A_79 | ~r1_tarski(B_78, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.87/2.26  tff(c_284, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_272])).
% 5.87/2.26  tff(c_2791, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2721, c_284])).
% 5.87/2.26  tff(c_2841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1000, c_2791])).
% 5.87/2.26  tff(c_2843, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 5.87/2.26  tff(c_3194, plain, (![A_370, B_371]: (k1_tops_1(A_370, B_371)=k1_xboole_0 | ~v2_tops_1(B_371, A_370) | ~m1_subset_1(B_371, k1_zfmisc_1(u1_struct_0(A_370))) | ~l1_pre_topc(A_370))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.87/2.26  tff(c_3197, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_3194])).
% 5.87/2.26  tff(c_3200, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2843, c_3197])).
% 5.87/2.26  tff(c_3788, plain, (![A_452, B_453]: (k7_subset_1(u1_struct_0(A_452), k2_pre_topc(A_452, B_453), k1_tops_1(A_452, B_453))=k2_tops_1(A_452, B_453) | ~m1_subset_1(B_453, k1_zfmisc_1(u1_struct_0(A_452))) | ~l1_pre_topc(A_452))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.87/2.26  tff(c_3797, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), k1_xboole_0)=k2_tops_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3200, c_3788])).
% 5.87/2.26  tff(c_3801, plain, (k7_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', '#skF_4'), k1_xboole_0)=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3797])).
% 5.87/2.26  tff(c_4966, plain, (k4_xboole_0(k2_pre_topc('#skF_3', '#skF_4'), k1_xboole_0)=k2_tops_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4960, c_3801])).
% 5.87/2.26  tff(c_4982, plain, (k2_tops_1('#skF_3', '#skF_4')=k2_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2878, c_4966])).
% 5.87/2.26  tff(c_2842, plain, (~r1_tarski('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_56])).
% 5.87/2.26  tff(c_4990, plain, (~r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4982, c_2842])).
% 5.87/2.26  tff(c_4993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3065, c_4990])).
% 5.87/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.26  
% 5.87/2.26  Inference rules
% 5.87/2.26  ----------------------
% 5.87/2.26  #Ref     : 0
% 5.87/2.26  #Sup     : 1240
% 5.87/2.26  #Fact    : 0
% 5.87/2.26  #Define  : 0
% 5.87/2.26  #Split   : 21
% 5.87/2.26  #Chain   : 0
% 5.87/2.26  #Close   : 0
% 5.87/2.26  
% 5.87/2.26  Ordering : KBO
% 5.87/2.26  
% 5.87/2.26  Simplification rules
% 5.87/2.26  ----------------------
% 5.87/2.26  #Subsume      : 285
% 5.87/2.26  #Demod        : 438
% 5.87/2.26  #Tautology    : 379
% 5.87/2.26  #SimpNegUnit  : 4
% 5.87/2.26  #BackRed      : 29
% 5.87/2.26  
% 5.87/2.26  #Partial instantiations: 0
% 5.87/2.26  #Strategies tried      : 1
% 5.87/2.26  
% 5.87/2.26  Timing (in seconds)
% 5.87/2.26  ----------------------
% 5.87/2.26  Preprocessing        : 0.32
% 5.87/2.26  Parsing              : 0.17
% 5.87/2.26  CNF conversion       : 0.02
% 5.87/2.26  Main loop            : 1.02
% 5.87/2.26  Inferencing          : 0.34
% 5.87/2.26  Reduction            : 0.32
% 5.87/2.26  Demodulation         : 0.22
% 5.87/2.26  BG Simplification    : 0.04
% 5.87/2.26  Subsumption          : 0.25
% 5.87/2.26  Abstraction          : 0.05
% 5.87/2.26  MUC search           : 0.00
% 5.87/2.26  Cooper               : 0.00
% 5.87/2.26  Total                : 1.39
% 5.87/2.26  Index Insertion      : 0.00
% 5.87/2.26  Index Deletion       : 0.00
% 5.87/2.26  Index Matching       : 0.00
% 5.87/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
