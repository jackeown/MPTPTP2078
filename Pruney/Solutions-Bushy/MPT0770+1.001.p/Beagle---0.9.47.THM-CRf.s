%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0770+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:50 EST 2020

% Result     : Theorem 51.12s
% Output     : CNFRefutation 51.43s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 395 expanded)
%              Number of leaves         :   41 ( 140 expanded)
%              Depth                    :   16
%              Number of atoms          :  259 ( 885 expanded)
%              Number of equality atoms :   17 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_wellord1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(A,k3_relat_1(k2_wellord1(C,B)))
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_wellord1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_72,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k8_relat_1(A_18,B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k7_relat_1(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_172,plain,(
    ! [A_85,B_86] :
      ( k8_relat_1(A_85,k7_relat_1(B_86,A_85)) = k2_wellord1(B_86,A_85)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_20,B_21)),k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_94237,plain,(
    ! [B_1142,A_1143] :
      ( r1_tarski(k1_relat_1(k2_wellord1(B_1142,A_1143)),k1_relat_1(k7_relat_1(B_1142,A_1143)))
      | ~ v1_relat_1(k7_relat_1(B_1142,A_1143))
      | ~ v1_relat_1(B_1142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_46])).

tff(c_201,plain,(
    ! [A_91,B_92] :
      ( k7_relat_1(k8_relat_1(A_91,B_92),A_91) = k2_wellord1(B_92,A_91)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_66,plain,(
    ! [B_41,A_40] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_41,A_40)),k2_relat_1(B_41))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_977,plain,(
    ! [B_199,A_200] :
      ( r1_tarski(k2_relat_1(k2_wellord1(B_199,A_200)),k2_relat_1(k8_relat_1(A_200,B_199)))
      | ~ v1_relat_1(k8_relat_1(A_200,B_199))
      | ~ v1_relat_1(B_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_66])).

tff(c_40,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k2_wellord1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,(
    r2_hidden('#skF_5',k3_relat_1(k2_wellord1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    ! [A_13] :
      ( k2_xboole_0(k1_relat_1(A_13),k2_relat_1(A_13)) = k3_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_222,plain,(
    ! [D_93,B_94,A_95] :
      ( r2_hidden(D_93,B_94)
      | r2_hidden(D_93,A_95)
      | ~ r2_hidden(D_93,k2_xboole_0(A_95,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_670,plain,(
    ! [D_177,A_178] :
      ( r2_hidden(D_177,k2_relat_1(A_178))
      | r2_hidden(D_177,k1_relat_1(A_178))
      | ~ r2_hidden(D_177,k3_relat_1(A_178))
      | ~ v1_relat_1(A_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_222])).

tff(c_712,plain,
    ( r2_hidden('#skF_5',k2_relat_1(k2_wellord1('#skF_7','#skF_6')))
    | r2_hidden('#skF_5',k1_relat_1(k2_wellord1('#skF_7','#skF_6')))
    | ~ v1_relat_1(k2_wellord1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_70,c_670])).

tff(c_749,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_712])).

tff(c_752,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_749])).

tff(c_756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_752])).

tff(c_757,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k2_wellord1('#skF_7','#skF_6')))
    | r2_hidden('#skF_5',k2_relat_1(k2_wellord1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_712])).

tff(c_759,plain,(
    r2_hidden('#skF_5',k2_relat_1(k2_wellord1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_757])).

tff(c_58,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_104,plain,(
    ! [C_68,B_69,A_70] :
      ( ~ v1_xboole_0(C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_107,plain,(
    ! [B_31,A_70,A_30] :
      ( ~ v1_xboole_0(B_31)
      | ~ r2_hidden(A_70,A_30)
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_58,c_104])).

tff(c_765,plain,(
    ! [B_31] :
      ( ~ v1_xboole_0(B_31)
      | ~ r1_tarski(k2_relat_1(k2_wellord1('#skF_7','#skF_6')),B_31) ) ),
    inference(resolution,[status(thm)],[c_759,c_107])).

tff(c_985,plain,
    ( ~ v1_xboole_0(k2_relat_1(k8_relat_1('#skF_6','#skF_7')))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_977,c_765])).

tff(c_998,plain,
    ( ~ v1_xboole_0(k2_relat_1(k8_relat_1('#skF_6','#skF_7')))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_985])).

tff(c_1001,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_998])).

tff(c_1004,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_1001])).

tff(c_1008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1004])).

tff(c_1009,plain,(
    ~ v1_xboole_0(k2_relat_1(k8_relat_1('#skF_6','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_998])).

tff(c_48,plain,(
    ! [B_23,A_22] :
      ( k3_xboole_0(k2_relat_1(B_23),A_22) = k2_relat_1(k8_relat_1(A_22,B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_123,plain,(
    ! [A_77] :
      ( k2_xboole_0(k1_relat_1(A_77),k2_relat_1(A_77)) = k3_relat_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_257,plain,(
    ! [D_98,A_99] :
      ( ~ r2_hidden(D_98,k2_relat_1(A_99))
      | r2_hidden(D_98,k3_relat_1(A_99))
      | ~ v1_relat_1(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_4])).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_77,plain,(
    ~ r2_hidden('#skF_5',k3_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_264,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_257,c_77])).

tff(c_269,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_264])).

tff(c_1010,plain,(
    v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_998])).

tff(c_168,plain,(
    ! [A_82,C_83,B_84] :
      ( m1_subset_1(A_82,C_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(C_83))
      | ~ r2_hidden(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_171,plain,(
    ! [A_82,B_31,A_30] :
      ( m1_subset_1(A_82,B_31)
      | ~ r2_hidden(A_82,A_30)
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_58,c_168])).

tff(c_764,plain,(
    ! [B_31] :
      ( m1_subset_1('#skF_5',B_31)
      | ~ r1_tarski(k2_relat_1(k2_wellord1('#skF_7','#skF_6')),B_31) ) ),
    inference(resolution,[status(thm)],[c_759,c_171])).

tff(c_981,plain,
    ( m1_subset_1('#skF_5',k2_relat_1(k8_relat_1('#skF_6','#skF_7')))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_977,c_764])).

tff(c_995,plain,
    ( m1_subset_1('#skF_5',k2_relat_1(k8_relat_1('#skF_6','#skF_7')))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_981])).

tff(c_1057,plain,(
    m1_subset_1('#skF_5',k2_relat_1(k8_relat_1('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_995])).

tff(c_86,plain,(
    ! [A_61,B_62] :
      ( r2_hidden(A_61,B_62)
      | v1_xboole_0(B_62)
      | ~ m1_subset_1(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    ! [D_12,A_7,B_8] :
      ( r2_hidden(D_12,A_7)
      | ~ r2_hidden(D_12,k3_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_463,plain,(
    ! [A_149,A_150,B_151] :
      ( r2_hidden(A_149,A_150)
      | v1_xboole_0(k3_xboole_0(A_150,B_151))
      | ~ m1_subset_1(A_149,k3_xboole_0(A_150,B_151)) ) ),
    inference(resolution,[status(thm)],[c_86,c_24])).

tff(c_94163,plain,(
    ! [A_1134,B_1135,A_1136] :
      ( r2_hidden(A_1134,k2_relat_1(B_1135))
      | v1_xboole_0(k3_xboole_0(k2_relat_1(B_1135),A_1136))
      | ~ m1_subset_1(A_1134,k2_relat_1(k8_relat_1(A_1136,B_1135)))
      | ~ v1_relat_1(B_1135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_463])).

tff(c_94192,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_7'))
    | v1_xboole_0(k3_xboole_0(k2_relat_1('#skF_7'),'#skF_6'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1057,c_94163])).

tff(c_94209,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_7'))
    | v1_xboole_0(k3_xboole_0(k2_relat_1('#skF_7'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_94192])).

tff(c_94210,plain,(
    v1_xboole_0(k3_xboole_0(k2_relat_1('#skF_7'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_94209])).

tff(c_94213,plain,
    ( v1_xboole_0(k2_relat_1(k8_relat_1('#skF_6','#skF_7')))
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_94210])).

tff(c_94215,plain,(
    v1_xboole_0(k2_relat_1(k8_relat_1('#skF_6','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_94213])).

tff(c_94217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1009,c_94215])).

tff(c_94218,plain,(
    r2_hidden('#skF_5',k1_relat_1(k2_wellord1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_757])).

tff(c_94225,plain,(
    ! [B_31] :
      ( ~ v1_xboole_0(B_31)
      | ~ r1_tarski(k1_relat_1(k2_wellord1('#skF_7','#skF_6')),B_31) ) ),
    inference(resolution,[status(thm)],[c_94218,c_107])).

tff(c_94245,plain,
    ( ~ v1_xboole_0(k1_relat_1(k7_relat_1('#skF_7','#skF_6')))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_94237,c_94225])).

tff(c_94258,plain,
    ( ~ v1_xboole_0(k1_relat_1(k7_relat_1('#skF_7','#skF_6')))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_94245])).

tff(c_94394,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_94258])).

tff(c_94397,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_94394])).

tff(c_94401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_94397])).

tff(c_94402,plain,(
    ~ v1_xboole_0(k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_94258])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_239,plain,(
    ! [D_96,A_97] :
      ( ~ r2_hidden(D_96,k1_relat_1(A_97))
      | r2_hidden(D_96,k3_relat_1(A_97))
      | ~ v1_relat_1(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_6])).

tff(c_246,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_239,c_77])).

tff(c_251,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_246])).

tff(c_94403,plain,(
    v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_94258])).

tff(c_94224,plain,(
    ! [B_31] :
      ( m1_subset_1('#skF_5',B_31)
      | ~ r1_tarski(k1_relat_1(k2_wellord1('#skF_7','#skF_6')),B_31) ) ),
    inference(resolution,[status(thm)],[c_94218,c_171])).

tff(c_94241,plain,
    ( m1_subset_1('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6')))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_94237,c_94224])).

tff(c_94255,plain,
    ( m1_subset_1('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6')))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_94241])).

tff(c_94405,plain,(
    m1_subset_1('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94403,c_94255])).

tff(c_54,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | v1_xboole_0(B_29)
      | ~ m1_subset_1(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_153,plain,(
    ! [B_80,A_81] :
      ( k3_xboole_0(k1_relat_1(B_80),A_81) = k1_relat_1(k7_relat_1(B_80,A_81))
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_449,plain,(
    ! [D_146,B_147,A_148] :
      ( r2_hidden(D_146,k1_relat_1(B_147))
      | ~ r2_hidden(D_146,k1_relat_1(k7_relat_1(B_147,A_148)))
      | ~ v1_relat_1(B_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_24])).

tff(c_181686,plain,(
    ! [A_2059,B_2060,A_2061] :
      ( r2_hidden(A_2059,k1_relat_1(B_2060))
      | ~ v1_relat_1(B_2060)
      | v1_xboole_0(k1_relat_1(k7_relat_1(B_2060,A_2061)))
      | ~ m1_subset_1(A_2059,k1_relat_1(k7_relat_1(B_2060,A_2061))) ) ),
    inference(resolution,[status(thm)],[c_54,c_449])).

tff(c_181715,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7')
    | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_94405,c_181686])).

tff(c_181732,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_181715])).

tff(c_181734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94402,c_251,c_181732])).

tff(c_181735,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_181909,plain,(
    ! [D_2119,B_2120,A_2121] :
      ( r2_hidden(D_2119,B_2120)
      | r2_hidden(D_2119,A_2121)
      | ~ r2_hidden(D_2119,k2_xboole_0(A_2121,B_2120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_182232,plain,(
    ! [D_2188,A_2189] :
      ( r2_hidden(D_2188,k2_relat_1(A_2189))
      | r2_hidden(D_2188,k1_relat_1(A_2189))
      | ~ r2_hidden(D_2188,k3_relat_1(A_2189))
      | ~ v1_relat_1(A_2189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_181909])).

tff(c_182270,plain,
    ( r2_hidden('#skF_5',k2_relat_1(k2_wellord1('#skF_7','#skF_6')))
    | r2_hidden('#skF_5',k1_relat_1(k2_wellord1('#skF_7','#skF_6')))
    | ~ v1_relat_1(k2_wellord1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_70,c_182232])).

tff(c_182388,plain,(
    ~ v1_relat_1(k2_wellord1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_182270])).

tff(c_182391,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_182388])).

tff(c_182395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_182391])).

tff(c_182396,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k2_wellord1('#skF_7','#skF_6')))
    | r2_hidden('#skF_5',k2_relat_1(k2_wellord1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_182270])).

tff(c_182398,plain,(
    r2_hidden('#skF_5',k2_relat_1(k2_wellord1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_182396])).

tff(c_52,plain,(
    ! [A_26,B_27] :
      ( k8_relat_1(A_26,k7_relat_1(B_27,A_26)) = k2_wellord1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_181838,plain,(
    ! [B_2101,A_2102] :
      ( k3_xboole_0(k2_relat_1(B_2101),A_2102) = k2_relat_1(k8_relat_1(A_2102,B_2101))
      | ~ v1_relat_1(B_2101) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k3_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_181988,plain,(
    ! [D_2134,A_2135,B_2136] :
      ( r2_hidden(D_2134,A_2135)
      | ~ r2_hidden(D_2134,k2_relat_1(k8_relat_1(A_2135,B_2136)))
      | ~ v1_relat_1(B_2136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181838,c_22])).

tff(c_183019,plain,(
    ! [D_2245,A_2246,B_2247] :
      ( r2_hidden(D_2245,A_2246)
      | ~ r2_hidden(D_2245,k2_relat_1(k2_wellord1(B_2247,A_2246)))
      | ~ v1_relat_1(k7_relat_1(B_2247,A_2246))
      | ~ v1_relat_1(B_2247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_181988])).

tff(c_183042,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_182398,c_183019])).

tff(c_183074,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_183042])).

tff(c_183075,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_181735,c_183074])).

tff(c_183237,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_183075])).

tff(c_183241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_183237])).

tff(c_183242,plain,(
    r2_hidden('#skF_5',k1_relat_1(k2_wellord1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_182396])).

tff(c_50,plain,(
    ! [A_24,B_25] :
      ( k7_relat_1(k8_relat_1(A_24,B_25),A_24) = k2_wellord1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_181853,plain,(
    ! [B_2103,A_2104] :
      ( k3_xboole_0(k1_relat_1(B_2103),A_2104) = k1_relat_1(k7_relat_1(B_2103,A_2104))
      | ~ v1_relat_1(B_2103) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_181954,plain,(
    ! [D_2128,A_2129,B_2130] :
      ( r2_hidden(D_2128,A_2129)
      | ~ r2_hidden(D_2128,k1_relat_1(k7_relat_1(B_2130,A_2129)))
      | ~ v1_relat_1(B_2130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181853,c_22])).

tff(c_183755,plain,(
    ! [D_2285,A_2286,B_2287] :
      ( r2_hidden(D_2285,A_2286)
      | ~ r2_hidden(D_2285,k1_relat_1(k2_wellord1(B_2287,A_2286)))
      | ~ v1_relat_1(k8_relat_1(A_2286,B_2287))
      | ~ v1_relat_1(B_2287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_181954])).

tff(c_183778,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_183242,c_183755])).

tff(c_183810,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_183778])).

tff(c_183811,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_181735,c_183810])).

tff(c_183820,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_183811])).

tff(c_183824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_183820])).

%------------------------------------------------------------------------------
