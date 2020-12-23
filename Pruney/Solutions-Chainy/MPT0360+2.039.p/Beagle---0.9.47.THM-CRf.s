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
% DateTime   : Thu Dec  3 09:56:23 EST 2020

% Result     : Theorem 17.65s
% Output     : CNFRefutation 17.65s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 574 expanded)
%              Number of leaves         :   32 ( 199 expanded)
%              Depth                    :   15
%              Number of atoms          :  173 (1225 expanded)
%              Number of equality atoms :   49 ( 257 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26683,plain,(
    ! [A_583,B_584] :
      ( r2_hidden('#skF_1'(A_583,B_584),A_583)
      | r1_tarski(A_583,B_584) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26703,plain,(
    ! [A_587] : r1_tarski(A_587,A_587) ),
    inference(resolution,[status(thm)],[c_26683,c_4])).

tff(c_26595,plain,(
    ! [A_564,C_565,B_566] :
      ( r1_xboole_0(A_564,C_565)
      | ~ r1_tarski(A_564,k4_xboole_0(B_566,C_565)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26601,plain,(
    ! [C_567] : r1_xboole_0(k1_xboole_0,C_567) ),
    inference(resolution,[status(thm)],[c_14,c_26595])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26605,plain,(
    ! [C_567] : k4_xboole_0(k1_xboole_0,C_567) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26601,c_18])).

tff(c_26646,plain,(
    ! [A_578,C_579,B_580] :
      ( r1_xboole_0(A_578,k4_xboole_0(C_579,B_580))
      | ~ r1_tarski(A_578,B_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26652,plain,(
    ! [A_578,C_567] :
      ( r1_xboole_0(A_578,k1_xboole_0)
      | ~ r1_tarski(A_578,C_567) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26605,c_26646])).

tff(c_26724,plain,(
    ! [A_588] : r1_xboole_0(A_588,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26703,c_26652])).

tff(c_26728,plain,(
    ! [A_588] : k4_xboole_0(A_588,k1_xboole_0) = A_588 ),
    inference(resolution,[status(thm)],[c_26724,c_18])).

tff(c_26,plain,(
    ! [C_23,A_19] :
      ( r2_hidden(C_23,k1_zfmisc_1(A_19))
      | ~ r1_tarski(C_23,A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26694,plain,(
    ! [B_585,A_586] :
      ( m1_subset_1(B_585,A_586)
      | ~ r2_hidden(B_585,A_586)
      | v1_xboole_0(A_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32237,plain,(
    ! [C_753,A_754] :
      ( m1_subset_1(C_753,k1_zfmisc_1(A_754))
      | v1_xboole_0(k1_zfmisc_1(A_754))
      | ~ r1_tarski(C_753,A_754) ) ),
    inference(resolution,[status(thm)],[c_26,c_26694])).

tff(c_44,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k3_subset_1(A_26,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_49200,plain,(
    ! [A_1027,C_1028] :
      ( k4_xboole_0(A_1027,C_1028) = k3_subset_1(A_1027,C_1028)
      | v1_xboole_0(k1_zfmisc_1(A_1027))
      | ~ r1_tarski(C_1028,A_1027) ) ),
    inference(resolution,[status(thm)],[c_32237,c_44])).

tff(c_49264,plain,(
    ! [A_11] :
      ( k4_xboole_0(A_11,k1_xboole_0) = k3_subset_1(A_11,k1_xboole_0)
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_14,c_49200])).

tff(c_49320,plain,(
    ! [A_1029] :
      ( k3_subset_1(A_1029,k1_xboole_0) = A_1029
      | v1_xboole_0(k1_zfmisc_1(A_1029)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26728,c_49264])).

tff(c_26600,plain,(
    ! [C_565] : r1_xboole_0(k1_xboole_0,C_565) ),
    inference(resolution,[status(thm)],[c_14,c_26595])).

tff(c_26759,plain,(
    ! [B_590,A_591] :
      ( ~ r1_xboole_0(B_590,A_591)
      | ~ r1_tarski(B_590,A_591)
      | v1_xboole_0(B_590) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26771,plain,(
    ! [C_565] :
      ( ~ r1_tarski(k1_xboole_0,C_565)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26600,c_26759])).

tff(c_26780,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26771])).

tff(c_40,plain,(
    ! [B_25,A_24] :
      ( m1_subset_1(B_25,A_24)
      | ~ v1_xboole_0(B_25)
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_27513,plain,(
    ! [A_637,B_638] :
      ( k4_xboole_0(A_637,B_638) = k3_subset_1(A_637,B_638)
      | ~ m1_subset_1(B_638,k1_zfmisc_1(A_637)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36028,plain,(
    ! [A_829,B_830] :
      ( k4_xboole_0(A_829,B_830) = k3_subset_1(A_829,B_830)
      | ~ v1_xboole_0(B_830)
      | ~ v1_xboole_0(k1_zfmisc_1(A_829)) ) ),
    inference(resolution,[status(thm)],[c_40,c_27513])).

tff(c_36052,plain,(
    ! [A_829] :
      ( k4_xboole_0(A_829,k1_xboole_0) = k3_subset_1(A_829,k1_xboole_0)
      | ~ v1_xboole_0(k1_zfmisc_1(A_829)) ) ),
    inference(resolution,[status(thm)],[c_26780,c_36028])).

tff(c_36069,plain,(
    ! [A_829] :
      ( k3_subset_1(A_829,k1_xboole_0) = A_829
      | ~ v1_xboole_0(k1_zfmisc_1(A_829)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26728,c_36052])).

tff(c_49348,plain,(
    ! [A_1029] : k3_subset_1(A_1029,k1_xboole_0) = A_1029 ),
    inference(resolution,[status(thm)],[c_49320,c_36069])).

tff(c_48,plain,(
    ! [A_30,B_31] :
      ( k3_subset_1(A_30,k3_subset_1(A_30,B_31)) = B_31
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_61344,plain,(
    ! [A_1143,C_1144] :
      ( k3_subset_1(A_1143,k3_subset_1(A_1143,C_1144)) = C_1144
      | v1_xboole_0(k1_zfmisc_1(A_1143))
      | ~ r1_tarski(C_1144,A_1143) ) ),
    inference(resolution,[status(thm)],[c_32237,c_48])).

tff(c_61410,plain,(
    ! [A_1029] :
      ( k3_subset_1(A_1029,A_1029) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_1029))
      | ~ r1_tarski(k1_xboole_0,A_1029) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49348,c_61344])).

tff(c_61459,plain,(
    ! [A_1145] :
      ( k3_subset_1(A_1145,A_1145) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_1145)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_61410])).

tff(c_54,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26992,plain,(
    ! [A_610,B_611] :
      ( ~ r1_tarski(A_610,B_611)
      | v1_xboole_0(A_610)
      | k4_xboole_0(A_610,B_611) != A_610 ) ),
    inference(resolution,[status(thm)],[c_20,c_26759])).

tff(c_27018,plain,
    ( v1_xboole_0('#skF_5')
    | k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_54,c_26992])).

tff(c_27030,plain,(
    k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_27018])).

tff(c_52,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_27154,plain,(
    ! [A_620,B_621] :
      ( k4_xboole_0(A_620,B_621) = k3_subset_1(A_620,B_621)
      | ~ m1_subset_1(B_621,k1_zfmisc_1(A_620)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_27167,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_27154])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_tarski(A_8,k4_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_27356,plain,(
    ! [A_630] :
      ( r1_xboole_0(A_630,'#skF_6')
      | ~ r1_tarski(A_630,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27167,c_10])).

tff(c_27381,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_27356])).

tff(c_27402,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_27381,c_18])).

tff(c_27409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27030,c_27402])).

tff(c_27410,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_27018])).

tff(c_26692,plain,(
    ! [A_583] : r1_tarski(A_583,A_583) ),
    inference(resolution,[status(thm)],[c_26683,c_4])).

tff(c_27411,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_27018])).

tff(c_22,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_xboole_0(A_16,k4_xboole_0(C_18,B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_27481,plain,(
    ! [A_635] :
      ( r1_xboole_0(A_635,'#skF_5')
      | ~ r1_tarski(A_635,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27411,c_22])).

tff(c_27588,plain,(
    ! [A_641] :
      ( k4_xboole_0(A_641,'#skF_5') = A_641
      | ~ r1_tarski(A_641,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_27481,c_18])).

tff(c_27610,plain,(
    k4_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_26692,c_27588])).

tff(c_49266,plain,
    ( k4_xboole_0('#skF_6','#skF_5') = k3_subset_1('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_54,c_49200])).

tff(c_49319,plain,
    ( k3_subset_1('#skF_6','#skF_5') = '#skF_6'
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27610,c_49266])).

tff(c_49387,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_49319])).

tff(c_36067,plain,(
    ! [A_829] :
      ( k4_xboole_0(A_829,'#skF_5') = k3_subset_1(A_829,'#skF_5')
      | ~ v1_xboole_0(k1_zfmisc_1(A_829)) ) ),
    inference(resolution,[status(thm)],[c_27410,c_36028])).

tff(c_49402,plain,(
    k4_xboole_0('#skF_6','#skF_5') = k3_subset_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_49387,c_36067])).

tff(c_49417,plain,(
    k3_subset_1('#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27610,c_49402])).

tff(c_27842,plain,(
    ! [A_652,B_653] :
      ( k3_subset_1(A_652,k3_subset_1(A_652,B_653)) = B_653
      | ~ m1_subset_1(B_653,k1_zfmisc_1(A_652)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_27851,plain,(
    ! [A_652,B_25] :
      ( k3_subset_1(A_652,k3_subset_1(A_652,B_25)) = B_25
      | ~ v1_xboole_0(B_25)
      | ~ v1_xboole_0(k1_zfmisc_1(A_652)) ) ),
    inference(resolution,[status(thm)],[c_40,c_27842])).

tff(c_61085,plain,(
    ! [B_1140] :
      ( k3_subset_1('#skF_6',k3_subset_1('#skF_6',B_1140)) = B_1140
      | ~ v1_xboole_0(B_1140) ) ),
    inference(resolution,[status(thm)],[c_49387,c_27851])).

tff(c_61149,plain,
    ( k3_subset_1('#skF_6','#skF_6') = '#skF_5'
    | ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_49417,c_61085])).

tff(c_61188,plain,(
    k3_subset_1('#skF_6','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27410,c_61149])).

tff(c_61153,plain,
    ( k3_subset_1('#skF_6','#skF_6') = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_49348,c_61085])).

tff(c_61190,plain,(
    k3_subset_1('#skF_6','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26780,c_61153])).

tff(c_61269,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61188,c_61190])).

tff(c_61270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_61269])).

tff(c_61272,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_49319])).

tff(c_61515,plain,(
    k3_subset_1('#skF_6','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61459,c_61272])).

tff(c_61271,plain,(
    k3_subset_1('#skF_6','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_49319])).

tff(c_26702,plain,(
    ! [C_23,A_19] :
      ( m1_subset_1(C_23,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19))
      | ~ r1_tarski(C_23,A_19) ) ),
    inference(resolution,[status(thm)],[c_26,c_26694])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k3_subset_1(A_28,B_29),k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_61282,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_61271,c_46])).

tff(c_62175,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_61282])).

tff(c_62178,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_6'))
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_26702,c_62175])).

tff(c_62184,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62178])).

tff(c_62186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61272,c_62184])).

tff(c_62188,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_61282])).

tff(c_62227,plain,(
    k3_subset_1('#skF_6',k3_subset_1('#skF_6','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_62188,c_48])).

tff(c_62242,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61515,c_61271,c_62227])).

tff(c_62244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_62242])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.65/9.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.65/9.36  
% 17.65/9.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.65/9.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 17.65/9.36  
% 17.65/9.36  %Foreground sorts:
% 17.65/9.36  
% 17.65/9.36  
% 17.65/9.36  %Background operators:
% 17.65/9.36  
% 17.65/9.36  
% 17.65/9.36  %Foreground operators:
% 17.65/9.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.65/9.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.65/9.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.65/9.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.65/9.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.65/9.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.65/9.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.65/9.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 17.65/9.36  tff('#skF_5', type, '#skF_5': $i).
% 17.65/9.36  tff('#skF_6', type, '#skF_6': $i).
% 17.65/9.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.65/9.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.65/9.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.65/9.36  tff('#skF_4', type, '#skF_4': $i).
% 17.65/9.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.65/9.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.65/9.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.65/9.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.65/9.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.65/9.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.65/9.36  
% 17.65/9.38  tff(f_99, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 17.65/9.38  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 17.65/9.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 17.65/9.38  tff(f_40, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 17.65/9.38  tff(f_54, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 17.65/9.38  tff(f_58, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 17.65/9.38  tff(f_65, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 17.65/9.38  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 17.65/9.38  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 17.65/9.38  tff(f_50, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 17.65/9.38  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 17.65/9.38  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 17.65/9.38  tff(c_50, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_99])).
% 17.65/9.38  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.65/9.38  tff(c_26683, plain, (![A_583, B_584]: (r2_hidden('#skF_1'(A_583, B_584), A_583) | r1_tarski(A_583, B_584))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.65/9.38  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.65/9.38  tff(c_26703, plain, (![A_587]: (r1_tarski(A_587, A_587))), inference(resolution, [status(thm)], [c_26683, c_4])).
% 17.65/9.38  tff(c_26595, plain, (![A_564, C_565, B_566]: (r1_xboole_0(A_564, C_565) | ~r1_tarski(A_564, k4_xboole_0(B_566, C_565)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 17.65/9.38  tff(c_26601, plain, (![C_567]: (r1_xboole_0(k1_xboole_0, C_567))), inference(resolution, [status(thm)], [c_14, c_26595])).
% 17.65/9.38  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.65/9.38  tff(c_26605, plain, (![C_567]: (k4_xboole_0(k1_xboole_0, C_567)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26601, c_18])).
% 17.65/9.38  tff(c_26646, plain, (![A_578, C_579, B_580]: (r1_xboole_0(A_578, k4_xboole_0(C_579, B_580)) | ~r1_tarski(A_578, B_580))), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.65/9.38  tff(c_26652, plain, (![A_578, C_567]: (r1_xboole_0(A_578, k1_xboole_0) | ~r1_tarski(A_578, C_567))), inference(superposition, [status(thm), theory('equality')], [c_26605, c_26646])).
% 17.65/9.38  tff(c_26724, plain, (![A_588]: (r1_xboole_0(A_588, k1_xboole_0))), inference(resolution, [status(thm)], [c_26703, c_26652])).
% 17.65/9.38  tff(c_26728, plain, (![A_588]: (k4_xboole_0(A_588, k1_xboole_0)=A_588)), inference(resolution, [status(thm)], [c_26724, c_18])).
% 17.65/9.38  tff(c_26, plain, (![C_23, A_19]: (r2_hidden(C_23, k1_zfmisc_1(A_19)) | ~r1_tarski(C_23, A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.65/9.38  tff(c_26694, plain, (![B_585, A_586]: (m1_subset_1(B_585, A_586) | ~r2_hidden(B_585, A_586) | v1_xboole_0(A_586))), inference(cnfTransformation, [status(thm)], [f_78])).
% 17.65/9.38  tff(c_32237, plain, (![C_753, A_754]: (m1_subset_1(C_753, k1_zfmisc_1(A_754)) | v1_xboole_0(k1_zfmisc_1(A_754)) | ~r1_tarski(C_753, A_754))), inference(resolution, [status(thm)], [c_26, c_26694])).
% 17.65/9.38  tff(c_44, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k3_subset_1(A_26, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.65/9.38  tff(c_49200, plain, (![A_1027, C_1028]: (k4_xboole_0(A_1027, C_1028)=k3_subset_1(A_1027, C_1028) | v1_xboole_0(k1_zfmisc_1(A_1027)) | ~r1_tarski(C_1028, A_1027))), inference(resolution, [status(thm)], [c_32237, c_44])).
% 17.65/9.38  tff(c_49264, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=k3_subset_1(A_11, k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_14, c_49200])).
% 17.65/9.38  tff(c_49320, plain, (![A_1029]: (k3_subset_1(A_1029, k1_xboole_0)=A_1029 | v1_xboole_0(k1_zfmisc_1(A_1029)))), inference(demodulation, [status(thm), theory('equality')], [c_26728, c_49264])).
% 17.65/9.38  tff(c_26600, plain, (![C_565]: (r1_xboole_0(k1_xboole_0, C_565))), inference(resolution, [status(thm)], [c_14, c_26595])).
% 17.65/9.38  tff(c_26759, plain, (![B_590, A_591]: (~r1_xboole_0(B_590, A_591) | ~r1_tarski(B_590, A_591) | v1_xboole_0(B_590))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.65/9.38  tff(c_26771, plain, (![C_565]: (~r1_tarski(k1_xboole_0, C_565) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_26600, c_26759])).
% 17.65/9.38  tff(c_26780, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26771])).
% 17.65/9.38  tff(c_40, plain, (![B_25, A_24]: (m1_subset_1(B_25, A_24) | ~v1_xboole_0(B_25) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 17.65/9.38  tff(c_27513, plain, (![A_637, B_638]: (k4_xboole_0(A_637, B_638)=k3_subset_1(A_637, B_638) | ~m1_subset_1(B_638, k1_zfmisc_1(A_637)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.65/9.38  tff(c_36028, plain, (![A_829, B_830]: (k4_xboole_0(A_829, B_830)=k3_subset_1(A_829, B_830) | ~v1_xboole_0(B_830) | ~v1_xboole_0(k1_zfmisc_1(A_829)))), inference(resolution, [status(thm)], [c_40, c_27513])).
% 17.65/9.38  tff(c_36052, plain, (![A_829]: (k4_xboole_0(A_829, k1_xboole_0)=k3_subset_1(A_829, k1_xboole_0) | ~v1_xboole_0(k1_zfmisc_1(A_829)))), inference(resolution, [status(thm)], [c_26780, c_36028])).
% 17.65/9.38  tff(c_36069, plain, (![A_829]: (k3_subset_1(A_829, k1_xboole_0)=A_829 | ~v1_xboole_0(k1_zfmisc_1(A_829)))), inference(demodulation, [status(thm), theory('equality')], [c_26728, c_36052])).
% 17.65/9.38  tff(c_49348, plain, (![A_1029]: (k3_subset_1(A_1029, k1_xboole_0)=A_1029)), inference(resolution, [status(thm)], [c_49320, c_36069])).
% 17.65/9.38  tff(c_48, plain, (![A_30, B_31]: (k3_subset_1(A_30, k3_subset_1(A_30, B_31))=B_31 | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 17.65/9.38  tff(c_61344, plain, (![A_1143, C_1144]: (k3_subset_1(A_1143, k3_subset_1(A_1143, C_1144))=C_1144 | v1_xboole_0(k1_zfmisc_1(A_1143)) | ~r1_tarski(C_1144, A_1143))), inference(resolution, [status(thm)], [c_32237, c_48])).
% 17.65/9.38  tff(c_61410, plain, (![A_1029]: (k3_subset_1(A_1029, A_1029)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_1029)) | ~r1_tarski(k1_xboole_0, A_1029))), inference(superposition, [status(thm), theory('equality')], [c_49348, c_61344])).
% 17.65/9.38  tff(c_61459, plain, (![A_1145]: (k3_subset_1(A_1145, A_1145)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_1145)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_61410])).
% 17.65/9.38  tff(c_54, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 17.65/9.38  tff(c_20, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.65/9.38  tff(c_26992, plain, (![A_610, B_611]: (~r1_tarski(A_610, B_611) | v1_xboole_0(A_610) | k4_xboole_0(A_610, B_611)!=A_610)), inference(resolution, [status(thm)], [c_20, c_26759])).
% 17.65/9.38  tff(c_27018, plain, (v1_xboole_0('#skF_5') | k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(resolution, [status(thm)], [c_54, c_26992])).
% 17.65/9.38  tff(c_27030, plain, (k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(splitLeft, [status(thm)], [c_27018])).
% 17.65/9.38  tff(c_52, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 17.65/9.38  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 17.65/9.38  tff(c_27154, plain, (![A_620, B_621]: (k4_xboole_0(A_620, B_621)=k3_subset_1(A_620, B_621) | ~m1_subset_1(B_621, k1_zfmisc_1(A_620)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.65/9.38  tff(c_27167, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_27154])).
% 17.65/9.38  tff(c_10, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_tarski(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 17.65/9.38  tff(c_27356, plain, (![A_630]: (r1_xboole_0(A_630, '#skF_6') | ~r1_tarski(A_630, k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_27167, c_10])).
% 17.65/9.38  tff(c_27381, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_27356])).
% 17.65/9.38  tff(c_27402, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_27381, c_18])).
% 17.65/9.38  tff(c_27409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27030, c_27402])).
% 17.65/9.38  tff(c_27410, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_27018])).
% 17.65/9.38  tff(c_26692, plain, (![A_583]: (r1_tarski(A_583, A_583))), inference(resolution, [status(thm)], [c_26683, c_4])).
% 17.65/9.38  tff(c_27411, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_27018])).
% 17.65/9.38  tff(c_22, plain, (![A_16, C_18, B_17]: (r1_xboole_0(A_16, k4_xboole_0(C_18, B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.65/9.38  tff(c_27481, plain, (![A_635]: (r1_xboole_0(A_635, '#skF_5') | ~r1_tarski(A_635, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_27411, c_22])).
% 17.65/9.38  tff(c_27588, plain, (![A_641]: (k4_xboole_0(A_641, '#skF_5')=A_641 | ~r1_tarski(A_641, '#skF_6'))), inference(resolution, [status(thm)], [c_27481, c_18])).
% 17.65/9.38  tff(c_27610, plain, (k4_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_26692, c_27588])).
% 17.65/9.38  tff(c_49266, plain, (k4_xboole_0('#skF_6', '#skF_5')=k3_subset_1('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_49200])).
% 17.65/9.38  tff(c_49319, plain, (k3_subset_1('#skF_6', '#skF_5')='#skF_6' | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_27610, c_49266])).
% 17.65/9.38  tff(c_49387, plain, (v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_49319])).
% 17.65/9.38  tff(c_36067, plain, (![A_829]: (k4_xboole_0(A_829, '#skF_5')=k3_subset_1(A_829, '#skF_5') | ~v1_xboole_0(k1_zfmisc_1(A_829)))), inference(resolution, [status(thm)], [c_27410, c_36028])).
% 17.65/9.38  tff(c_49402, plain, (k4_xboole_0('#skF_6', '#skF_5')=k3_subset_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_49387, c_36067])).
% 17.65/9.38  tff(c_49417, plain, (k3_subset_1('#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_27610, c_49402])).
% 17.65/9.38  tff(c_27842, plain, (![A_652, B_653]: (k3_subset_1(A_652, k3_subset_1(A_652, B_653))=B_653 | ~m1_subset_1(B_653, k1_zfmisc_1(A_652)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 17.65/9.38  tff(c_27851, plain, (![A_652, B_25]: (k3_subset_1(A_652, k3_subset_1(A_652, B_25))=B_25 | ~v1_xboole_0(B_25) | ~v1_xboole_0(k1_zfmisc_1(A_652)))), inference(resolution, [status(thm)], [c_40, c_27842])).
% 17.65/9.38  tff(c_61085, plain, (![B_1140]: (k3_subset_1('#skF_6', k3_subset_1('#skF_6', B_1140))=B_1140 | ~v1_xboole_0(B_1140))), inference(resolution, [status(thm)], [c_49387, c_27851])).
% 17.65/9.38  tff(c_61149, plain, (k3_subset_1('#skF_6', '#skF_6')='#skF_5' | ~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_49417, c_61085])).
% 17.65/9.38  tff(c_61188, plain, (k3_subset_1('#skF_6', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_27410, c_61149])).
% 17.65/9.38  tff(c_61153, plain, (k3_subset_1('#skF_6', '#skF_6')=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_49348, c_61085])).
% 17.65/9.38  tff(c_61190, plain, (k3_subset_1('#skF_6', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26780, c_61153])).
% 17.65/9.38  tff(c_61269, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_61188, c_61190])).
% 17.65/9.38  tff(c_61270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_61269])).
% 17.65/9.38  tff(c_61272, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_49319])).
% 17.65/9.38  tff(c_61515, plain, (k3_subset_1('#skF_6', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_61459, c_61272])).
% 17.65/9.38  tff(c_61271, plain, (k3_subset_1('#skF_6', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_49319])).
% 17.65/9.38  tff(c_26702, plain, (![C_23, A_19]: (m1_subset_1(C_23, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)) | ~r1_tarski(C_23, A_19))), inference(resolution, [status(thm)], [c_26, c_26694])).
% 17.65/9.38  tff(c_46, plain, (![A_28, B_29]: (m1_subset_1(k3_subset_1(A_28, B_29), k1_zfmisc_1(A_28)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 17.65/9.38  tff(c_61282, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_61271, c_46])).
% 17.65/9.38  tff(c_62175, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_61282])).
% 17.65/9.38  tff(c_62178, plain, (v1_xboole_0(k1_zfmisc_1('#skF_6')) | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_26702, c_62175])).
% 17.65/9.38  tff(c_62184, plain, (v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62178])).
% 17.65/9.38  tff(c_62186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61272, c_62184])).
% 17.65/9.38  tff(c_62188, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_61282])).
% 17.65/9.38  tff(c_62227, plain, (k3_subset_1('#skF_6', k3_subset_1('#skF_6', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_62188, c_48])).
% 17.65/9.38  tff(c_62242, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_61515, c_61271, c_62227])).
% 17.65/9.38  tff(c_62244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_62242])).
% 17.65/9.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.65/9.38  
% 17.65/9.38  Inference rules
% 17.65/9.38  ----------------------
% 17.65/9.38  #Ref     : 0
% 17.65/9.38  #Sup     : 15200
% 17.65/9.38  #Fact    : 0
% 17.65/9.38  #Define  : 0
% 17.65/9.38  #Split   : 45
% 17.65/9.38  #Chain   : 0
% 17.65/9.38  #Close   : 0
% 17.65/9.38  
% 17.65/9.38  Ordering : KBO
% 17.65/9.38  
% 17.65/9.38  Simplification rules
% 17.65/9.38  ----------------------
% 17.65/9.38  #Subsume      : 3342
% 17.65/9.38  #Demod        : 11038
% 17.65/9.38  #Tautology    : 7842
% 17.65/9.38  #SimpNegUnit  : 56
% 17.65/9.38  #BackRed      : 101
% 17.65/9.38  
% 17.65/9.38  #Partial instantiations: 0
% 17.65/9.38  #Strategies tried      : 1
% 17.65/9.38  
% 17.65/9.38  Timing (in seconds)
% 17.65/9.38  ----------------------
% 17.65/9.38  Preprocessing        : 0.34
% 17.65/9.38  Parsing              : 0.18
% 17.65/9.38  CNF conversion       : 0.03
% 17.65/9.38  Main loop            : 8.22
% 17.65/9.38  Inferencing          : 1.51
% 17.65/9.38  Reduction            : 3.87
% 17.65/9.38  Demodulation         : 3.19
% 17.65/9.38  BG Simplification    : 0.14
% 17.65/9.38  Subsumption          : 2.29
% 17.65/9.38  Abstraction          : 0.20
% 17.65/9.38  MUC search           : 0.00
% 17.65/9.38  Cooper               : 0.00
% 17.65/9.38  Total                : 8.60
% 17.65/9.38  Index Insertion      : 0.00
% 17.65/9.38  Index Deletion       : 0.00
% 17.65/9.38  Index Matching       : 0.00
% 17.65/9.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
