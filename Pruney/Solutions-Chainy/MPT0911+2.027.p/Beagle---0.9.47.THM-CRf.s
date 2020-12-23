%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:05 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 650 expanded)
%              Number of leaves         :   37 ( 238 expanded)
%              Depth                    :   19
%              Number of atoms          :  302 (1833 expanded)
%              Number of equality atoms :  155 ( 864 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_624,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( k7_mcart_1(A_177,B_178,C_179,D_180) = k2_mcart_1(D_180)
      | ~ m1_subset_1(D_180,k3_zfmisc_1(A_177,B_178,C_179))
      | k1_xboole_0 = C_179
      | k1_xboole_0 = B_178
      | k1_xboole_0 = A_177 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_630,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_624])).

tff(c_633,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_630])).

tff(c_34,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_634,plain,(
    k2_mcart_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_34])).

tff(c_210,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k7_mcart_1(A_93,B_94,C_95,D_96) = k2_mcart_1(D_96)
      | ~ m1_subset_1(D_96,k3_zfmisc_1(A_93,B_94,C_95))
      | k1_xboole_0 = C_95
      | k1_xboole_0 = B_94
      | k1_xboole_0 = A_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_213,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_210])).

tff(c_216,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_213])).

tff(c_224,plain,(
    k2_mcart_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_34])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] : k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16) = k3_zfmisc_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_6] :
      ( v1_xboole_0(k1_relat_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_51,plain,(
    ! [A_44] :
      ( v1_xboole_0(k1_relat_1(A_44))
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_56,plain,(
    ! [A_45] :
      ( k1_relat_1(A_45) = k1_xboole_0
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_51,c_4])).

tff(c_62,plain,(
    ! [A_48] :
      ( k1_relat_1(k1_relat_1(A_48)) = k1_xboole_0
      | ~ v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_10,c_56])).

tff(c_71,plain,(
    ! [A_48] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_48))
      | ~ v1_xboole_0(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_10])).

tff(c_81,plain,(
    ! [A_49] :
      ( ~ v1_xboole_0(k1_relat_1(A_49))
      | ~ v1_xboole_0(A_49) ) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_88,plain,(
    ! [A_6] : ~ v1_xboole_0(A_6) ),
    inference(resolution,[status(thm)],[c_10,c_81])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_91,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_8])).

tff(c_131,plain,(
    ! [A_65,C_66,B_67] :
      ( r2_hidden(k2_mcart_1(A_65),C_66)
      | ~ r2_hidden(A_65,k2_zfmisc_1(B_67,C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_175,plain,(
    ! [A_75,C_76,B_77] :
      ( r2_hidden(k2_mcart_1(A_75),C_76)
      | ~ m1_subset_1(A_75,k2_zfmisc_1(B_77,C_76)) ) ),
    inference(resolution,[status(thm)],[c_91,c_131])).

tff(c_190,plain,(
    ! [A_87,C_88,A_89,B_90] :
      ( r2_hidden(k2_mcart_1(A_87),C_88)
      | ~ m1_subset_1(A_87,k3_zfmisc_1(A_89,B_90,C_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_175])).

tff(c_193,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_190])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_200,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_193,c_6])).

tff(c_97,plain,(
    ! [A_53,B_54,C_55] : k2_zfmisc_1(k2_zfmisc_1(A_53,B_54),C_55) = k3_zfmisc_1(A_53,B_54,C_55) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_105,plain,(
    ! [A_53,B_54,C_55] : v1_relat_1(k3_zfmisc_1(A_53,B_54,C_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_12])).

tff(c_186,plain,(
    ! [A_85,B_86] :
      ( k4_tarski(k1_mcart_1(A_85),k2_mcart_1(A_85)) = A_85
      | ~ r2_hidden(A_85,B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_201,plain,(
    ! [A_91,B_92] :
      ( k4_tarski(k1_mcart_1(A_91),k2_mcart_1(A_91)) = A_91
      | ~ v1_relat_1(B_92)
      | ~ m1_subset_1(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_91,c_186])).

tff(c_205,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_201])).

tff(c_209,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_205])).

tff(c_272,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k5_mcart_1(A_106,B_107,C_108,D_109) = k1_mcart_1(k1_mcart_1(D_109))
      | ~ m1_subset_1(D_109,k3_zfmisc_1(A_106,B_107,C_108))
      | k1_xboole_0 = C_108
      | k1_xboole_0 = B_107
      | k1_xboole_0 = A_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_278,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_272])).

tff(c_281,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_278])).

tff(c_168,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden(k1_mcart_1(A_72),B_73)
      | ~ r2_hidden(A_72,k2_zfmisc_1(B_73,C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_178,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden(k1_mcart_1(A_78),B_79)
      | ~ m1_subset_1(A_78,k2_zfmisc_1(B_79,C_80)) ) ),
    inference(resolution,[status(thm)],[c_91,c_168])).

tff(c_324,plain,(
    ! [A_117,A_118,B_119,C_120] :
      ( r2_hidden(k1_mcart_1(A_117),k2_zfmisc_1(A_118,B_119))
      | ~ m1_subset_1(A_117,k3_zfmisc_1(A_118,B_119,C_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_178])).

tff(c_330,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_324])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(k1_mcart_1(A_17),B_18)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_334,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_330,c_24])).

tff(c_344,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_334])).

tff(c_392,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_344,c_6])).

tff(c_347,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k6_mcart_1(A_121,B_122,C_123,D_124) = k2_mcart_1(k1_mcart_1(D_124))
      | ~ m1_subset_1(D_124,k3_zfmisc_1(A_121,B_122,C_123))
      | k1_xboole_0 = C_123
      | k1_xboole_0 = B_122
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_353,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_347])).

tff(c_356,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_353])).

tff(c_22,plain,(
    ! [A_17,C_19,B_18] :
      ( r2_hidden(k2_mcart_1(A_17),C_19)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_345,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_330,c_22])).

tff(c_381,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_345])).

tff(c_399,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_381,c_6])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k4_tarski(k1_mcart_1(A_20),k2_mcart_1(A_20)) = A_20
      | ~ r2_hidden(A_20,B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_332,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_330,c_26])).

tff(c_342,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_281,c_332])).

tff(c_422,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_342])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] : k4_tarski(k4_tarski(A_11,B_12),C_13) = k3_mcart_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_444,plain,(
    ! [C_132] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_132) = k4_tarski(k1_mcart_1('#skF_5'),C_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_18])).

tff(c_42,plain,(
    ! [H_40,F_34,G_38] :
      ( H_40 = '#skF_4'
      | k3_mcart_1(F_34,G_38,H_40) != '#skF_5'
      | ~ m1_subset_1(H_40,'#skF_3')
      | ~ m1_subset_1(G_38,'#skF_2')
      | ~ m1_subset_1(F_34,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_451,plain,(
    ! [C_132] :
      ( C_132 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_132) != '#skF_5'
      | ~ m1_subset_1(C_132,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_42])).

tff(c_465,plain,(
    ! [C_138] :
      ( C_138 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_138) != '#skF_5'
      | ~ m1_subset_1(C_138,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_399,c_451])).

tff(c_468,plain,
    ( k2_mcart_1('#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_465])).

tff(c_471,plain,(
    k2_mcart_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_468])).

tff(c_473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_471])).

tff(c_474,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_55,plain,(
    ! [A_44] :
      ( k1_relat_1(A_44) = k1_xboole_0
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_51,c_4])).

tff(c_481,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_474,c_55])).

tff(c_518,plain,(
    ! [A_146,B_147,C_148] : k2_zfmisc_1(k2_zfmisc_1(A_146,B_147),C_148) = k3_zfmisc_1(A_146,B_147,C_148) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_529,plain,(
    ! [A_146,B_147,C_148] : v1_relat_1(k3_zfmisc_1(A_146,B_147,C_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_12])).

tff(c_598,plain,(
    ! [A_169,B_170] :
      ( k4_tarski(k1_mcart_1(A_169),k2_mcart_1(A_169)) = A_169
      | ~ r2_hidden(A_169,B_170)
      | ~ v1_relat_1(B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_708,plain,(
    ! [A_200,B_201] :
      ( k4_tarski(k1_mcart_1(A_200),k2_mcart_1(A_200)) = A_200
      | ~ v1_relat_1(B_201)
      | v1_xboole_0(B_201)
      | ~ m1_subset_1(A_200,B_201) ) ),
    inference(resolution,[status(thm)],[c_8,c_598])).

tff(c_710,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_708])).

tff(c_713,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_710])).

tff(c_714,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_713])).

tff(c_726,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_714,c_4])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k2_relat_1(k2_zfmisc_1(A_9,B_10)) = B_10
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_527,plain,(
    ! [A_146,B_147,C_148] :
      ( k2_relat_1(k3_zfmisc_1(A_146,B_147,C_148)) = C_148
      | k1_xboole_0 = C_148
      | k2_zfmisc_1(A_146,B_147) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_14])).

tff(c_741,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_527])).

tff(c_753,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_741])).

tff(c_766,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_753])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k1_relat_1(k2_zfmisc_1(A_9,B_10)) = A_9
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_781,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_16])).

tff(c_803,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_781])).

tff(c_805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_40,c_803])).

tff(c_807,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_753])).

tff(c_571,plain,(
    ! [A_161,B_162] :
      ( k1_relat_1(k2_zfmisc_1(A_161,B_162)) = A_161
      | k1_xboole_0 = B_162
      | k1_xboole_0 = A_161 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_966,plain,(
    ! [A_222,B_223,C_224] :
      ( k1_relat_1(k3_zfmisc_1(A_222,B_223,C_224)) = k2_zfmisc_1(A_222,B_223)
      | k1_xboole_0 = C_224
      | k2_zfmisc_1(A_222,B_223) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_571])).

tff(c_981,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_966])).

tff(c_987,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_981])).

tff(c_989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_807,c_36,c_807,c_987])).

tff(c_991,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_713])).

tff(c_561,plain,(
    ! [A_158,C_159,B_160] :
      ( r2_hidden(k2_mcart_1(A_158),C_159)
      | ~ r2_hidden(A_158,k2_zfmisc_1(B_160,C_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1015,plain,(
    ! [A_226,C_227,B_228] :
      ( r2_hidden(k2_mcart_1(A_226),C_227)
      | v1_xboole_0(k2_zfmisc_1(B_228,C_227))
      | ~ m1_subset_1(A_226,k2_zfmisc_1(B_228,C_227)) ) ),
    inference(resolution,[status(thm)],[c_8,c_561])).

tff(c_1017,plain,(
    ! [A_226,C_16,A_14,B_15] :
      ( r2_hidden(k2_mcart_1(A_226),C_16)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16))
      | ~ m1_subset_1(A_226,k3_zfmisc_1(A_14,B_15,C_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1015])).

tff(c_1043,plain,(
    ! [A_235,C_236,A_237,B_238] :
      ( r2_hidden(k2_mcart_1(A_235),C_236)
      | v1_xboole_0(k3_zfmisc_1(A_237,B_238,C_236))
      | ~ m1_subset_1(A_235,k3_zfmisc_1(A_237,B_238,C_236)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1017])).

tff(c_1047,plain,
    ( r2_hidden(k2_mcart_1('#skF_5'),'#skF_3')
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_1043])).

tff(c_1051,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_991,c_1047])).

tff(c_1058,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1051,c_6])).

tff(c_990,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_713])).

tff(c_655,plain,(
    ! [A_184,B_185,C_186,D_187] :
      ( k5_mcart_1(A_184,B_185,C_186,D_187) = k1_mcart_1(k1_mcart_1(D_187))
      | ~ m1_subset_1(D_187,k3_zfmisc_1(A_184,B_185,C_186))
      | k1_xboole_0 = C_186
      | k1_xboole_0 = B_185
      | k1_xboole_0 = A_184 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_661,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_655])).

tff(c_664,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_661])).

tff(c_538,plain,(
    ! [A_149,B_150,C_151] :
      ( r2_hidden(k1_mcart_1(A_149),B_150)
      | ~ r2_hidden(A_149,k2_zfmisc_1(B_150,C_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1019,plain,(
    ! [A_229,B_230,C_231] :
      ( r2_hidden(k1_mcart_1(A_229),B_230)
      | v1_xboole_0(k2_zfmisc_1(B_230,C_231))
      | ~ m1_subset_1(A_229,k2_zfmisc_1(B_230,C_231)) ) ),
    inference(resolution,[status(thm)],[c_8,c_538])).

tff(c_1021,plain,(
    ! [A_229,A_14,B_15,C_16] :
      ( r2_hidden(k1_mcart_1(A_229),k2_zfmisc_1(A_14,B_15))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16))
      | ~ m1_subset_1(A_229,k3_zfmisc_1(A_14,B_15,C_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1019])).

tff(c_1075,plain,(
    ! [A_246,A_247,B_248,C_249] :
      ( r2_hidden(k1_mcart_1(A_246),k2_zfmisc_1(A_247,B_248))
      | v1_xboole_0(k3_zfmisc_1(A_247,B_248,C_249))
      | ~ m1_subset_1(A_246,k3_zfmisc_1(A_247,B_248,C_249)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1021])).

tff(c_1079,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_1075])).

tff(c_1083,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_991,c_1079])).

tff(c_1089,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1083,c_24])).

tff(c_1099,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_1089])).

tff(c_1127,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1099,c_6])).

tff(c_694,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( k6_mcart_1(A_196,B_197,C_198,D_199) = k2_mcart_1(k1_mcart_1(D_199))
      | ~ m1_subset_1(D_199,k3_zfmisc_1(A_196,B_197,C_198))
      | k1_xboole_0 = C_198
      | k1_xboole_0 = B_197
      | k1_xboole_0 = A_196 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_700,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_694])).

tff(c_703,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_700])).

tff(c_1087,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1083,c_22])).

tff(c_1097,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_1087])).

tff(c_1120,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1097,c_6])).

tff(c_1085,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1083,c_26])).

tff(c_1095,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_664,c_703,c_1085])).

tff(c_1151,plain,(
    ! [C_253] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_253) = k4_tarski(k1_mcart_1('#skF_5'),C_253) ),
    inference(superposition,[status(thm),theory(equality)],[c_1095,c_18])).

tff(c_1158,plain,(
    ! [C_253] :
      ( C_253 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_253) != '#skF_5'
      | ~ m1_subset_1(C_253,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_42])).

tff(c_1167,plain,(
    ! [C_254] :
      ( C_254 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_254) != '#skF_5'
      | ~ m1_subset_1(C_254,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1127,c_1120,c_1158])).

tff(c_1170,plain,
    ( k2_mcart_1('#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_990,c_1167])).

tff(c_1173,plain,(
    k2_mcart_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_1170])).

tff(c_1175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_634,c_1173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:04:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.56  
% 3.36/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.56  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.36/1.56  
% 3.36/1.56  %Foreground sorts:
% 3.36/1.56  
% 3.36/1.56  
% 3.36/1.56  %Background operators:
% 3.36/1.56  
% 3.36/1.56  
% 3.36/1.56  %Foreground operators:
% 3.36/1.56  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.36/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.36/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.56  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.36/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.36/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.56  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.36/1.56  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.36/1.56  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.36/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.56  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.36/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.56  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.36/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.56  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.36/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.36/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.36/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.56  
% 3.36/1.58  tff(f_118, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 3.36/1.58  tff(f_94, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.36/1.58  tff(f_62, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.36/1.58  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.36/1.58  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.36/1.58  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.36/1.58  tff(f_68, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.36/1.58  tff(f_34, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.36/1.58  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.36/1.58  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 3.36/1.58  tff(f_60, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.36/1.58  tff(f_58, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 3.36/1.58  tff(c_40, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.36/1.58  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.36/1.58  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.36/1.58  tff(c_44, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.36/1.58  tff(c_624, plain, (![A_177, B_178, C_179, D_180]: (k7_mcart_1(A_177, B_178, C_179, D_180)=k2_mcart_1(D_180) | ~m1_subset_1(D_180, k3_zfmisc_1(A_177, B_178, C_179)) | k1_xboole_0=C_179 | k1_xboole_0=B_178 | k1_xboole_0=A_177)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.36/1.58  tff(c_630, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_44, c_624])).
% 3.36/1.58  tff(c_633, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_630])).
% 3.36/1.58  tff(c_34, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.36/1.58  tff(c_634, plain, (k2_mcart_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_633, c_34])).
% 3.36/1.58  tff(c_210, plain, (![A_93, B_94, C_95, D_96]: (k7_mcart_1(A_93, B_94, C_95, D_96)=k2_mcart_1(D_96) | ~m1_subset_1(D_96, k3_zfmisc_1(A_93, B_94, C_95)) | k1_xboole_0=C_95 | k1_xboole_0=B_94 | k1_xboole_0=A_93)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.36/1.58  tff(c_213, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_44, c_210])).
% 3.36/1.58  tff(c_216, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_213])).
% 3.36/1.58  tff(c_224, plain, (k2_mcart_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_216, c_34])).
% 3.36/1.58  tff(c_20, plain, (![A_14, B_15, C_16]: (k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.36/1.58  tff(c_10, plain, (![A_6]: (v1_xboole_0(k1_relat_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.36/1.58  tff(c_51, plain, (![A_44]: (v1_xboole_0(k1_relat_1(A_44)) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.36/1.58  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.36/1.58  tff(c_56, plain, (![A_45]: (k1_relat_1(A_45)=k1_xboole_0 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_51, c_4])).
% 3.36/1.58  tff(c_62, plain, (![A_48]: (k1_relat_1(k1_relat_1(A_48))=k1_xboole_0 | ~v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_10, c_56])).
% 3.36/1.58  tff(c_71, plain, (![A_48]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_48)) | ~v1_xboole_0(A_48))), inference(superposition, [status(thm), theory('equality')], [c_62, c_10])).
% 3.36/1.58  tff(c_81, plain, (![A_49]: (~v1_xboole_0(k1_relat_1(A_49)) | ~v1_xboole_0(A_49))), inference(splitLeft, [status(thm)], [c_71])).
% 3.36/1.58  tff(c_88, plain, (![A_6]: (~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_10, c_81])).
% 3.36/1.58  tff(c_8, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.36/1.58  tff(c_91, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | ~m1_subset_1(A_4, B_5))), inference(negUnitSimplification, [status(thm)], [c_88, c_8])).
% 3.36/1.58  tff(c_131, plain, (![A_65, C_66, B_67]: (r2_hidden(k2_mcart_1(A_65), C_66) | ~r2_hidden(A_65, k2_zfmisc_1(B_67, C_66)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.36/1.58  tff(c_175, plain, (![A_75, C_76, B_77]: (r2_hidden(k2_mcart_1(A_75), C_76) | ~m1_subset_1(A_75, k2_zfmisc_1(B_77, C_76)))), inference(resolution, [status(thm)], [c_91, c_131])).
% 3.36/1.58  tff(c_190, plain, (![A_87, C_88, A_89, B_90]: (r2_hidden(k2_mcart_1(A_87), C_88) | ~m1_subset_1(A_87, k3_zfmisc_1(A_89, B_90, C_88)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_175])).
% 3.36/1.58  tff(c_193, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_44, c_190])).
% 3.36/1.58  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.36/1.58  tff(c_200, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_193, c_6])).
% 3.36/1.58  tff(c_97, plain, (![A_53, B_54, C_55]: (k2_zfmisc_1(k2_zfmisc_1(A_53, B_54), C_55)=k3_zfmisc_1(A_53, B_54, C_55))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.36/1.58  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.36/1.58  tff(c_105, plain, (![A_53, B_54, C_55]: (v1_relat_1(k3_zfmisc_1(A_53, B_54, C_55)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_12])).
% 3.36/1.58  tff(c_186, plain, (![A_85, B_86]: (k4_tarski(k1_mcart_1(A_85), k2_mcart_1(A_85))=A_85 | ~r2_hidden(A_85, B_86) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.36/1.58  tff(c_201, plain, (![A_91, B_92]: (k4_tarski(k1_mcart_1(A_91), k2_mcart_1(A_91))=A_91 | ~v1_relat_1(B_92) | ~m1_subset_1(A_91, B_92))), inference(resolution, [status(thm)], [c_91, c_186])).
% 3.36/1.58  tff(c_205, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_201])).
% 3.36/1.58  tff(c_209, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_205])).
% 3.36/1.58  tff(c_272, plain, (![A_106, B_107, C_108, D_109]: (k5_mcart_1(A_106, B_107, C_108, D_109)=k1_mcart_1(k1_mcart_1(D_109)) | ~m1_subset_1(D_109, k3_zfmisc_1(A_106, B_107, C_108)) | k1_xboole_0=C_108 | k1_xboole_0=B_107 | k1_xboole_0=A_106)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.36/1.58  tff(c_278, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_44, c_272])).
% 3.36/1.58  tff(c_281, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_278])).
% 3.36/1.58  tff(c_168, plain, (![A_72, B_73, C_74]: (r2_hidden(k1_mcart_1(A_72), B_73) | ~r2_hidden(A_72, k2_zfmisc_1(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.36/1.58  tff(c_178, plain, (![A_78, B_79, C_80]: (r2_hidden(k1_mcart_1(A_78), B_79) | ~m1_subset_1(A_78, k2_zfmisc_1(B_79, C_80)))), inference(resolution, [status(thm)], [c_91, c_168])).
% 3.36/1.58  tff(c_324, plain, (![A_117, A_118, B_119, C_120]: (r2_hidden(k1_mcart_1(A_117), k2_zfmisc_1(A_118, B_119)) | ~m1_subset_1(A_117, k3_zfmisc_1(A_118, B_119, C_120)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_178])).
% 3.36/1.58  tff(c_330, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_324])).
% 3.36/1.58  tff(c_24, plain, (![A_17, B_18, C_19]: (r2_hidden(k1_mcart_1(A_17), B_18) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.36/1.58  tff(c_334, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_330, c_24])).
% 3.36/1.58  tff(c_344, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_334])).
% 3.36/1.58  tff(c_392, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_344, c_6])).
% 3.36/1.58  tff(c_347, plain, (![A_121, B_122, C_123, D_124]: (k6_mcart_1(A_121, B_122, C_123, D_124)=k2_mcart_1(k1_mcart_1(D_124)) | ~m1_subset_1(D_124, k3_zfmisc_1(A_121, B_122, C_123)) | k1_xboole_0=C_123 | k1_xboole_0=B_122 | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.36/1.58  tff(c_353, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_44, c_347])).
% 3.36/1.58  tff(c_356, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_353])).
% 3.36/1.58  tff(c_22, plain, (![A_17, C_19, B_18]: (r2_hidden(k2_mcart_1(A_17), C_19) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.36/1.58  tff(c_345, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_330, c_22])).
% 3.36/1.58  tff(c_381, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_345])).
% 3.36/1.58  tff(c_399, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_381, c_6])).
% 3.36/1.58  tff(c_26, plain, (![A_20, B_21]: (k4_tarski(k1_mcart_1(A_20), k2_mcart_1(A_20))=A_20 | ~r2_hidden(A_20, B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.36/1.58  tff(c_332, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_330, c_26])).
% 3.36/1.58  tff(c_342, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_281, c_332])).
% 3.36/1.58  tff(c_422, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_342])).
% 3.36/1.58  tff(c_18, plain, (![A_11, B_12, C_13]: (k4_tarski(k4_tarski(A_11, B_12), C_13)=k3_mcart_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.36/1.58  tff(c_444, plain, (![C_132]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_132)=k4_tarski(k1_mcart_1('#skF_5'), C_132))), inference(superposition, [status(thm), theory('equality')], [c_422, c_18])).
% 3.36/1.58  tff(c_42, plain, (![H_40, F_34, G_38]: (H_40='#skF_4' | k3_mcart_1(F_34, G_38, H_40)!='#skF_5' | ~m1_subset_1(H_40, '#skF_3') | ~m1_subset_1(G_38, '#skF_2') | ~m1_subset_1(F_34, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.36/1.58  tff(c_451, plain, (![C_132]: (C_132='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_132)!='#skF_5' | ~m1_subset_1(C_132, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_42])).
% 3.36/1.58  tff(c_465, plain, (![C_138]: (C_138='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_138)!='#skF_5' | ~m1_subset_1(C_138, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_399, c_451])).
% 3.36/1.58  tff(c_468, plain, (k2_mcart_1('#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_209, c_465])).
% 3.36/1.58  tff(c_471, plain, (k2_mcart_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_468])).
% 3.36/1.58  tff(c_473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_471])).
% 3.36/1.58  tff(c_474, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_71])).
% 3.36/1.58  tff(c_55, plain, (![A_44]: (k1_relat_1(A_44)=k1_xboole_0 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_51, c_4])).
% 3.36/1.58  tff(c_481, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_474, c_55])).
% 3.36/1.58  tff(c_518, plain, (![A_146, B_147, C_148]: (k2_zfmisc_1(k2_zfmisc_1(A_146, B_147), C_148)=k3_zfmisc_1(A_146, B_147, C_148))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.36/1.58  tff(c_529, plain, (![A_146, B_147, C_148]: (v1_relat_1(k3_zfmisc_1(A_146, B_147, C_148)))), inference(superposition, [status(thm), theory('equality')], [c_518, c_12])).
% 3.36/1.58  tff(c_598, plain, (![A_169, B_170]: (k4_tarski(k1_mcart_1(A_169), k2_mcart_1(A_169))=A_169 | ~r2_hidden(A_169, B_170) | ~v1_relat_1(B_170))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.36/1.58  tff(c_708, plain, (![A_200, B_201]: (k4_tarski(k1_mcart_1(A_200), k2_mcart_1(A_200))=A_200 | ~v1_relat_1(B_201) | v1_xboole_0(B_201) | ~m1_subset_1(A_200, B_201))), inference(resolution, [status(thm)], [c_8, c_598])).
% 3.36/1.58  tff(c_710, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_708])).
% 3.36/1.58  tff(c_713, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_529, c_710])).
% 3.36/1.58  tff(c_714, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_713])).
% 3.36/1.58  tff(c_726, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_714, c_4])).
% 3.36/1.58  tff(c_14, plain, (![A_9, B_10]: (k2_relat_1(k2_zfmisc_1(A_9, B_10))=B_10 | k1_xboole_0=B_10 | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.36/1.58  tff(c_527, plain, (![A_146, B_147, C_148]: (k2_relat_1(k3_zfmisc_1(A_146, B_147, C_148))=C_148 | k1_xboole_0=C_148 | k2_zfmisc_1(A_146, B_147)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_518, c_14])).
% 3.36/1.58  tff(c_741, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_726, c_527])).
% 3.36/1.58  tff(c_753, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_36, c_741])).
% 3.36/1.58  tff(c_766, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_753])).
% 3.36/1.58  tff(c_16, plain, (![A_9, B_10]: (k1_relat_1(k2_zfmisc_1(A_9, B_10))=A_9 | k1_xboole_0=B_10 | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.36/1.58  tff(c_781, plain, (k1_relat_1(k1_xboole_0)='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_766, c_16])).
% 3.36/1.58  tff(c_803, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_481, c_781])).
% 3.36/1.58  tff(c_805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_40, c_803])).
% 3.36/1.58  tff(c_807, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_753])).
% 3.36/1.58  tff(c_571, plain, (![A_161, B_162]: (k1_relat_1(k2_zfmisc_1(A_161, B_162))=A_161 | k1_xboole_0=B_162 | k1_xboole_0=A_161)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.36/1.58  tff(c_966, plain, (![A_222, B_223, C_224]: (k1_relat_1(k3_zfmisc_1(A_222, B_223, C_224))=k2_zfmisc_1(A_222, B_223) | k1_xboole_0=C_224 | k2_zfmisc_1(A_222, B_223)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_571])).
% 3.36/1.58  tff(c_981, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_relat_1(k1_xboole_0) | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_726, c_966])).
% 3.36/1.58  tff(c_987, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_481, c_981])).
% 3.36/1.58  tff(c_989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_807, c_36, c_807, c_987])).
% 3.36/1.58  tff(c_991, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_713])).
% 3.36/1.58  tff(c_561, plain, (![A_158, C_159, B_160]: (r2_hidden(k2_mcart_1(A_158), C_159) | ~r2_hidden(A_158, k2_zfmisc_1(B_160, C_159)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.36/1.58  tff(c_1015, plain, (![A_226, C_227, B_228]: (r2_hidden(k2_mcart_1(A_226), C_227) | v1_xboole_0(k2_zfmisc_1(B_228, C_227)) | ~m1_subset_1(A_226, k2_zfmisc_1(B_228, C_227)))), inference(resolution, [status(thm)], [c_8, c_561])).
% 3.36/1.58  tff(c_1017, plain, (![A_226, C_16, A_14, B_15]: (r2_hidden(k2_mcart_1(A_226), C_16) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)) | ~m1_subset_1(A_226, k3_zfmisc_1(A_14, B_15, C_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1015])).
% 3.36/1.58  tff(c_1043, plain, (![A_235, C_236, A_237, B_238]: (r2_hidden(k2_mcart_1(A_235), C_236) | v1_xboole_0(k3_zfmisc_1(A_237, B_238, C_236)) | ~m1_subset_1(A_235, k3_zfmisc_1(A_237, B_238, C_236)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1017])).
% 3.36/1.58  tff(c_1047, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3') | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_1043])).
% 3.36/1.58  tff(c_1051, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_991, c_1047])).
% 3.36/1.58  tff(c_1058, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_1051, c_6])).
% 3.36/1.58  tff(c_990, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_713])).
% 3.36/1.58  tff(c_655, plain, (![A_184, B_185, C_186, D_187]: (k5_mcart_1(A_184, B_185, C_186, D_187)=k1_mcart_1(k1_mcart_1(D_187)) | ~m1_subset_1(D_187, k3_zfmisc_1(A_184, B_185, C_186)) | k1_xboole_0=C_186 | k1_xboole_0=B_185 | k1_xboole_0=A_184)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.36/1.58  tff(c_661, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_44, c_655])).
% 3.36/1.58  tff(c_664, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_661])).
% 3.36/1.58  tff(c_538, plain, (![A_149, B_150, C_151]: (r2_hidden(k1_mcart_1(A_149), B_150) | ~r2_hidden(A_149, k2_zfmisc_1(B_150, C_151)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.36/1.58  tff(c_1019, plain, (![A_229, B_230, C_231]: (r2_hidden(k1_mcart_1(A_229), B_230) | v1_xboole_0(k2_zfmisc_1(B_230, C_231)) | ~m1_subset_1(A_229, k2_zfmisc_1(B_230, C_231)))), inference(resolution, [status(thm)], [c_8, c_538])).
% 3.36/1.58  tff(c_1021, plain, (![A_229, A_14, B_15, C_16]: (r2_hidden(k1_mcart_1(A_229), k2_zfmisc_1(A_14, B_15)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)) | ~m1_subset_1(A_229, k3_zfmisc_1(A_14, B_15, C_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1019])).
% 3.36/1.58  tff(c_1075, plain, (![A_246, A_247, B_248, C_249]: (r2_hidden(k1_mcart_1(A_246), k2_zfmisc_1(A_247, B_248)) | v1_xboole_0(k3_zfmisc_1(A_247, B_248, C_249)) | ~m1_subset_1(A_246, k3_zfmisc_1(A_247, B_248, C_249)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1021])).
% 3.36/1.58  tff(c_1079, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_1075])).
% 3.36/1.58  tff(c_1083, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_991, c_1079])).
% 3.36/1.58  tff(c_1089, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_1083, c_24])).
% 3.36/1.58  tff(c_1099, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_664, c_1089])).
% 3.36/1.58  tff(c_1127, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_1099, c_6])).
% 3.36/1.58  tff(c_694, plain, (![A_196, B_197, C_198, D_199]: (k6_mcart_1(A_196, B_197, C_198, D_199)=k2_mcart_1(k1_mcart_1(D_199)) | ~m1_subset_1(D_199, k3_zfmisc_1(A_196, B_197, C_198)) | k1_xboole_0=C_198 | k1_xboole_0=B_197 | k1_xboole_0=A_196)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.36/1.58  tff(c_700, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_44, c_694])).
% 3.36/1.58  tff(c_703, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_700])).
% 3.36/1.58  tff(c_1087, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_1083, c_22])).
% 3.36/1.58  tff(c_1097, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_703, c_1087])).
% 3.36/1.58  tff(c_1120, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_1097, c_6])).
% 3.36/1.58  tff(c_1085, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1083, c_26])).
% 3.36/1.58  tff(c_1095, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_664, c_703, c_1085])).
% 3.36/1.58  tff(c_1151, plain, (![C_253]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_253)=k4_tarski(k1_mcart_1('#skF_5'), C_253))), inference(superposition, [status(thm), theory('equality')], [c_1095, c_18])).
% 3.36/1.58  tff(c_1158, plain, (![C_253]: (C_253='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_253)!='#skF_5' | ~m1_subset_1(C_253, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1151, c_42])).
% 3.36/1.58  tff(c_1167, plain, (![C_254]: (C_254='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_254)!='#skF_5' | ~m1_subset_1(C_254, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1127, c_1120, c_1158])).
% 3.36/1.58  tff(c_1170, plain, (k2_mcart_1('#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_990, c_1167])).
% 3.36/1.58  tff(c_1173, plain, (k2_mcart_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1058, c_1170])).
% 3.36/1.58  tff(c_1175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_634, c_1173])).
% 3.36/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.58  
% 3.36/1.58  Inference rules
% 3.36/1.58  ----------------------
% 3.36/1.58  #Ref     : 0
% 3.36/1.58  #Sup     : 287
% 3.36/1.58  #Fact    : 0
% 3.36/1.58  #Define  : 0
% 3.36/1.58  #Split   : 9
% 3.36/1.58  #Chain   : 0
% 3.36/1.58  #Close   : 0
% 3.36/1.58  
% 3.36/1.58  Ordering : KBO
% 3.36/1.58  
% 3.36/1.58  Simplification rules
% 3.36/1.58  ----------------------
% 3.36/1.58  #Subsume      : 43
% 3.36/1.58  #Demod        : 123
% 3.36/1.58  #Tautology    : 108
% 3.36/1.58  #SimpNegUnit  : 20
% 3.36/1.58  #BackRed      : 6
% 3.36/1.58  
% 3.36/1.58  #Partial instantiations: 0
% 3.36/1.58  #Strategies tried      : 1
% 3.36/1.58  
% 3.36/1.58  Timing (in seconds)
% 3.36/1.58  ----------------------
% 3.36/1.59  Preprocessing        : 0.32
% 3.36/1.59  Parsing              : 0.17
% 3.36/1.59  CNF conversion       : 0.02
% 3.36/1.59  Main loop            : 0.45
% 3.36/1.59  Inferencing          : 0.18
% 3.36/1.59  Reduction            : 0.14
% 3.36/1.59  Demodulation         : 0.09
% 3.36/1.59  BG Simplification    : 0.02
% 3.36/1.59  Subsumption          : 0.08
% 3.36/1.59  Abstraction          : 0.02
% 3.36/1.59  MUC search           : 0.00
% 3.36/1.59  Cooper               : 0.00
% 3.36/1.59  Total                : 0.82
% 3.36/1.59  Index Insertion      : 0.00
% 3.36/1.59  Index Deletion       : 0.00
% 3.36/1.59  Index Matching       : 0.00
% 3.36/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
