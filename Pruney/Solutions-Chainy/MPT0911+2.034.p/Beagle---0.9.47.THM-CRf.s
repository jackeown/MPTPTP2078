%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:06 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 563 expanded)
%              Number of leaves         :   36 ( 210 expanded)
%              Depth                    :   17
%              Number of atoms          :  279 (1621 expanded)
%              Number of equality atoms :  139 ( 746 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_117,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_575,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( k7_mcart_1(A_163,B_164,C_165,D_166) = k2_mcart_1(D_166)
      | ~ m1_subset_1(D_166,k3_zfmisc_1(A_163,B_164,C_165))
      | k1_xboole_0 = C_165
      | k1_xboole_0 = B_164
      | k1_xboole_0 = A_163 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_578,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_575])).

tff(c_581,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_578])).

tff(c_32,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_582,plain,(
    k2_mcart_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_32])).

tff(c_184,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( k7_mcart_1(A_87,B_88,C_89,D_90) = k2_mcart_1(D_90)
      | ~ m1_subset_1(D_90,k3_zfmisc_1(A_87,B_88,C_89))
      | k1_xboole_0 = C_89
      | k1_xboole_0 = B_88
      | k1_xboole_0 = A_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_187,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_184])).

tff(c_190,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_187])).

tff(c_191,plain,(
    k2_mcart_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_32])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] : k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16) = k3_zfmisc_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_xboole_0(k2_relat_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    ! [A_44] :
      ( v1_xboole_0(k2_relat_1(A_44))
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    ! [A_45] :
      ( k2_relat_1(A_45) = k1_xboole_0
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_57,plain,(
    ! [A_51] :
      ( k2_relat_1(k2_relat_1(A_51)) = k1_xboole_0
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_8,c_50])).

tff(c_66,plain,(
    ! [A_51] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_51))
      | ~ v1_xboole_0(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_8])).

tff(c_76,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(k2_relat_1(A_52))
      | ~ v1_xboole_0(A_52) ) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_83,plain,(
    ! [A_6] : ~ v1_xboole_0(A_6) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_6])).

tff(c_104,plain,(
    ! [A_58,C_59,B_60] :
      ( r2_hidden(k2_mcart_1(A_58),C_59)
      | ~ r2_hidden(A_58,k2_zfmisc_1(B_60,C_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_173,plain,(
    ! [A_77,C_78,B_79] :
      ( r2_hidden(k2_mcart_1(A_77),C_78)
      | ~ m1_subset_1(A_77,k2_zfmisc_1(B_79,C_78)) ) ),
    inference(resolution,[status(thm)],[c_86,c_104])).

tff(c_196,plain,(
    ! [A_91,C_92,A_93,B_94] :
      ( r2_hidden(k2_mcart_1(A_91),C_92)
      | ~ m1_subset_1(A_91,k3_zfmisc_1(A_93,B_94,C_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_173])).

tff(c_199,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_196])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_206,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_199,c_4])).

tff(c_136,plain,(
    ! [A_66,B_67,C_68] : k2_zfmisc_1(k2_zfmisc_1(A_66,B_67),C_68) = k3_zfmisc_1(A_66,B_67,C_68) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_152,plain,(
    ! [A_66,B_67,C_68] : v1_relat_1(k3_zfmisc_1(A_66,B_67,C_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_10])).

tff(c_169,plain,(
    ! [A_75,B_76] :
      ( k4_tarski(k1_mcart_1(A_75),k2_mcart_1(A_75)) = A_75
      | ~ r2_hidden(A_75,B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_218,plain,(
    ! [A_99,B_100] :
      ( k4_tarski(k1_mcart_1(A_99),k2_mcart_1(A_99)) = A_99
      | ~ v1_relat_1(B_100)
      | ~ m1_subset_1(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_86,c_169])).

tff(c_222,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_218])).

tff(c_226,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_222])).

tff(c_207,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k5_mcart_1(A_95,B_96,C_97,D_98) = k1_mcart_1(k1_mcart_1(D_98))
      | ~ m1_subset_1(D_98,k3_zfmisc_1(A_95,B_96,C_97))
      | k1_xboole_0 = C_97
      | k1_xboole_0 = B_96
      | k1_xboole_0 = A_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_210,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_207])).

tff(c_213,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_210])).

tff(c_162,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden(k1_mcart_1(A_72),B_73)
      | ~ r2_hidden(A_72,k2_zfmisc_1(B_73,C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_246,plain,(
    ! [A_102,A_103,B_104,C_105] :
      ( r2_hidden(k1_mcart_1(A_102),k2_zfmisc_1(A_103,B_104))
      | ~ r2_hidden(A_102,k3_zfmisc_1(A_103,B_104,C_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_162])).

tff(c_332,plain,(
    ! [A_121,A_122,B_123,C_124] :
      ( r2_hidden(k1_mcart_1(A_121),k2_zfmisc_1(A_122,B_123))
      | ~ m1_subset_1(A_121,k3_zfmisc_1(A_122,B_123,C_124)) ) ),
    inference(resolution,[status(thm)],[c_86,c_246])).

tff(c_338,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_332])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(k1_mcart_1(A_17),B_18)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_356,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_338,c_22])).

tff(c_366,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_356])).

tff(c_389,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_366,c_4])).

tff(c_251,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k6_mcart_1(A_106,B_107,C_108,D_109) = k2_mcart_1(k1_mcart_1(D_109))
      | ~ m1_subset_1(D_109,k3_zfmisc_1(A_106,B_107,C_108))
      | k1_xboole_0 = C_108
      | k1_xboole_0 = B_107
      | k1_xboole_0 = A_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_254,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_251])).

tff(c_257,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_254])).

tff(c_20,plain,(
    ! [A_17,C_19,B_18] :
      ( r2_hidden(k2_mcart_1(A_17),C_19)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_358,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_338,c_20])).

tff(c_368,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_358])).

tff(c_403,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_368,c_4])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( k4_tarski(k1_mcart_1(A_20),k2_mcart_1(A_20)) = A_20
      | ~ r2_hidden(A_20,B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_354,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_338,c_24])).

tff(c_364,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_257,c_213,c_354])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : k4_tarski(k4_tarski(A_11,B_12),C_13) = k3_mcart_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_423,plain,(
    ! [C_132] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_132) = k4_tarski(k1_mcart_1('#skF_5'),C_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_16])).

tff(c_40,plain,(
    ! [H_40,F_34,G_38] :
      ( H_40 = '#skF_4'
      | k3_mcart_1(F_34,G_38,H_40) != '#skF_5'
      | ~ m1_subset_1(H_40,'#skF_3')
      | ~ m1_subset_1(G_38,'#skF_2')
      | ~ m1_subset_1(F_34,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_430,plain,(
    ! [C_132] :
      ( C_132 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_132) != '#skF_5'
      | ~ m1_subset_1(C_132,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_40])).

tff(c_439,plain,(
    ! [C_133] :
      ( C_133 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_133) != '#skF_5'
      | ~ m1_subset_1(C_133,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_403,c_430])).

tff(c_442,plain,
    ( k2_mcart_1('#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_439])).

tff(c_445,plain,(
    k2_mcart_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_442])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_445])).

tff(c_448,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_49,plain,(
    ! [A_44] :
      ( k2_relat_1(A_44) = k1_xboole_0
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_455,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_448,c_49])).

tff(c_534,plain,(
    ! [A_149,B_150,C_151] : k2_zfmisc_1(k2_zfmisc_1(A_149,B_150),C_151) = k3_zfmisc_1(A_149,B_150,C_151) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_552,plain,(
    ! [A_149,B_150,C_151] : v1_relat_1(k3_zfmisc_1(A_149,B_150,C_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_10])).

tff(c_571,plain,(
    ! [A_161,B_162] :
      ( k4_tarski(k1_mcart_1(A_161),k2_mcart_1(A_161)) = A_161
      | ~ r2_hidden(A_161,B_162)
      | ~ v1_relat_1(B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_695,plain,(
    ! [A_199,B_200] :
      ( k4_tarski(k1_mcart_1(A_199),k2_mcart_1(A_199)) = A_199
      | ~ v1_relat_1(B_200)
      | v1_xboole_0(B_200)
      | ~ m1_subset_1(A_199,B_200) ) ),
    inference(resolution,[status(thm)],[c_6,c_571])).

tff(c_697,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_695])).

tff(c_700,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_697])).

tff(c_701,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_700])).

tff(c_709,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_701,c_2])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_relat_1(k2_zfmisc_1(A_9,B_10)) = B_10
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_543,plain,(
    ! [A_149,B_150,C_151] :
      ( k2_relat_1(k3_zfmisc_1(A_149,B_150,C_151)) = C_151
      | k1_xboole_0 = C_151
      | k2_zfmisc_1(A_149,B_150) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_12])).

tff(c_716,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_543])).

tff(c_734,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_716])).

tff(c_735,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_734])).

tff(c_768,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_735,c_12])).

tff(c_788,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_768])).

tff(c_790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_36,c_788])).

tff(c_792,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_700])).

tff(c_566,plain,(
    ! [A_157,C_158,A_159,B_160] :
      ( r2_hidden(k2_mcart_1(A_157),C_158)
      | ~ r2_hidden(A_157,k3_zfmisc_1(A_159,B_160,C_158)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_20])).

tff(c_847,plain,(
    ! [A_217,C_218,A_219,B_220] :
      ( r2_hidden(k2_mcart_1(A_217),C_218)
      | v1_xboole_0(k3_zfmisc_1(A_219,B_220,C_218))
      | ~ m1_subset_1(A_217,k3_zfmisc_1(A_219,B_220,C_218)) ) ),
    inference(resolution,[status(thm)],[c_6,c_566])).

tff(c_851,plain,
    ( r2_hidden(k2_mcart_1('#skF_5'),'#skF_3')
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_847])).

tff(c_855,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_792,c_851])).

tff(c_862,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_855,c_4])).

tff(c_791,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_700])).

tff(c_591,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( k5_mcart_1(A_169,B_170,C_171,D_172) = k1_mcart_1(k1_mcart_1(D_172))
      | ~ m1_subset_1(D_172,k3_zfmisc_1(A_169,B_170,C_171))
      | k1_xboole_0 = C_171
      | k1_xboole_0 = B_170
      | k1_xboole_0 = A_169 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_594,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_591])).

tff(c_597,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_594])).

tff(c_496,plain,(
    ! [A_141,B_142,C_143] :
      ( r2_hidden(k1_mcart_1(A_141),B_142)
      | ~ r2_hidden(A_141,k2_zfmisc_1(B_142,C_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_691,plain,(
    ! [A_196,B_197,C_198] :
      ( r2_hidden(k1_mcart_1(A_196),B_197)
      | v1_xboole_0(k2_zfmisc_1(B_197,C_198))
      | ~ m1_subset_1(A_196,k2_zfmisc_1(B_197,C_198)) ) ),
    inference(resolution,[status(thm)],[c_6,c_496])).

tff(c_693,plain,(
    ! [A_196,A_14,B_15,C_16] :
      ( r2_hidden(k1_mcart_1(A_196),k2_zfmisc_1(A_14,B_15))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16))
      | ~ m1_subset_1(A_196,k3_zfmisc_1(A_14,B_15,C_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_691])).

tff(c_867,plain,(
    ! [A_221,A_222,B_223,C_224] :
      ( r2_hidden(k1_mcart_1(A_221),k2_zfmisc_1(A_222,B_223))
      | v1_xboole_0(k3_zfmisc_1(A_222,B_223,C_224))
      | ~ m1_subset_1(A_221,k3_zfmisc_1(A_222,B_223,C_224)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_693])).

tff(c_871,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_867])).

tff(c_875,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_792,c_871])).

tff(c_879,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_875,c_22])).

tff(c_889,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_879])).

tff(c_912,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_889,c_4])).

tff(c_650,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( k6_mcart_1(A_185,B_186,C_187,D_188) = k2_mcart_1(k1_mcart_1(D_188))
      | ~ m1_subset_1(D_188,k3_zfmisc_1(A_185,B_186,C_187))
      | k1_xboole_0 = C_187
      | k1_xboole_0 = B_186
      | k1_xboole_0 = A_185 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_656,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_650])).

tff(c_659,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_656])).

tff(c_881,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_875,c_20])).

tff(c_891,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_881])).

tff(c_919,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_891,c_4])).

tff(c_877,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_875,c_24])).

tff(c_887,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_597,c_659,c_877])).

tff(c_938,plain,(
    ! [C_225] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_225) = k4_tarski(k1_mcart_1('#skF_5'),C_225) ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_16])).

tff(c_945,plain,(
    ! [C_225] :
      ( C_225 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_225) != '#skF_5'
      | ~ m1_subset_1(C_225,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_938,c_40])).

tff(c_954,plain,(
    ! [C_226] :
      ( C_226 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_226) != '#skF_5'
      | ~ m1_subset_1(C_226,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_919,c_945])).

tff(c_957,plain,
    ( k2_mcart_1('#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_954])).

tff(c_960,plain,(
    k2_mcart_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_957])).

tff(c_962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_960])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 18:48:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.47  
% 3.11/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.47  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.11/1.47  
% 3.11/1.47  %Foreground sorts:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Background operators:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Foreground operators:
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.11/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.47  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.11/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.11/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.47  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.11/1.47  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.11/1.47  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.47  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.11/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.11/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.47  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.47  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.11/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.11/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.47  
% 3.26/1.50  tff(f_117, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 3.26/1.50  tff(f_93, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.26/1.50  tff(f_61, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.26/1.50  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 3.26/1.50  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.26/1.50  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.26/1.50  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.26/1.50  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.26/1.50  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.26/1.50  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 3.26/1.50  tff(f_59, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.26/1.50  tff(f_57, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 3.26/1.50  tff(c_38, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.26/1.50  tff(c_36, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.26/1.50  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.26/1.50  tff(c_42, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.26/1.50  tff(c_575, plain, (![A_163, B_164, C_165, D_166]: (k7_mcart_1(A_163, B_164, C_165, D_166)=k2_mcart_1(D_166) | ~m1_subset_1(D_166, k3_zfmisc_1(A_163, B_164, C_165)) | k1_xboole_0=C_165 | k1_xboole_0=B_164 | k1_xboole_0=A_163)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.50  tff(c_578, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_42, c_575])).
% 3.26/1.50  tff(c_581, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_578])).
% 3.26/1.50  tff(c_32, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.26/1.50  tff(c_582, plain, (k2_mcart_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_581, c_32])).
% 3.26/1.50  tff(c_184, plain, (![A_87, B_88, C_89, D_90]: (k7_mcart_1(A_87, B_88, C_89, D_90)=k2_mcart_1(D_90) | ~m1_subset_1(D_90, k3_zfmisc_1(A_87, B_88, C_89)) | k1_xboole_0=C_89 | k1_xboole_0=B_88 | k1_xboole_0=A_87)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.50  tff(c_187, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_42, c_184])).
% 3.26/1.50  tff(c_190, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_187])).
% 3.26/1.50  tff(c_191, plain, (k2_mcart_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_32])).
% 3.26/1.50  tff(c_18, plain, (![A_14, B_15, C_16]: (k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.26/1.50  tff(c_8, plain, (![A_6]: (v1_xboole_0(k2_relat_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.50  tff(c_45, plain, (![A_44]: (v1_xboole_0(k2_relat_1(A_44)) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.50  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.50  tff(c_50, plain, (![A_45]: (k2_relat_1(A_45)=k1_xboole_0 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_45, c_2])).
% 3.26/1.50  tff(c_57, plain, (![A_51]: (k2_relat_1(k2_relat_1(A_51))=k1_xboole_0 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_8, c_50])).
% 3.26/1.50  tff(c_66, plain, (![A_51]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_51)) | ~v1_xboole_0(A_51))), inference(superposition, [status(thm), theory('equality')], [c_57, c_8])).
% 3.26/1.50  tff(c_76, plain, (![A_52]: (~v1_xboole_0(k2_relat_1(A_52)) | ~v1_xboole_0(A_52))), inference(splitLeft, [status(thm)], [c_66])).
% 3.26/1.50  tff(c_83, plain, (![A_6]: (~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_8, c_76])).
% 3.26/1.50  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.50  tff(c_86, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | ~m1_subset_1(A_4, B_5))), inference(negUnitSimplification, [status(thm)], [c_83, c_6])).
% 3.26/1.50  tff(c_104, plain, (![A_58, C_59, B_60]: (r2_hidden(k2_mcart_1(A_58), C_59) | ~r2_hidden(A_58, k2_zfmisc_1(B_60, C_59)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.50  tff(c_173, plain, (![A_77, C_78, B_79]: (r2_hidden(k2_mcart_1(A_77), C_78) | ~m1_subset_1(A_77, k2_zfmisc_1(B_79, C_78)))), inference(resolution, [status(thm)], [c_86, c_104])).
% 3.26/1.50  tff(c_196, plain, (![A_91, C_92, A_93, B_94]: (r2_hidden(k2_mcart_1(A_91), C_92) | ~m1_subset_1(A_91, k3_zfmisc_1(A_93, B_94, C_92)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_173])).
% 3.26/1.50  tff(c_199, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_42, c_196])).
% 3.26/1.50  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(A_2, B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.50  tff(c_206, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_199, c_4])).
% 3.26/1.50  tff(c_136, plain, (![A_66, B_67, C_68]: (k2_zfmisc_1(k2_zfmisc_1(A_66, B_67), C_68)=k3_zfmisc_1(A_66, B_67, C_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.26/1.50  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.50  tff(c_152, plain, (![A_66, B_67, C_68]: (v1_relat_1(k3_zfmisc_1(A_66, B_67, C_68)))), inference(superposition, [status(thm), theory('equality')], [c_136, c_10])).
% 3.26/1.50  tff(c_169, plain, (![A_75, B_76]: (k4_tarski(k1_mcart_1(A_75), k2_mcart_1(A_75))=A_75 | ~r2_hidden(A_75, B_76) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.26/1.50  tff(c_218, plain, (![A_99, B_100]: (k4_tarski(k1_mcart_1(A_99), k2_mcart_1(A_99))=A_99 | ~v1_relat_1(B_100) | ~m1_subset_1(A_99, B_100))), inference(resolution, [status(thm)], [c_86, c_169])).
% 3.26/1.50  tff(c_222, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_218])).
% 3.26/1.50  tff(c_226, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_222])).
% 3.26/1.50  tff(c_207, plain, (![A_95, B_96, C_97, D_98]: (k5_mcart_1(A_95, B_96, C_97, D_98)=k1_mcart_1(k1_mcart_1(D_98)) | ~m1_subset_1(D_98, k3_zfmisc_1(A_95, B_96, C_97)) | k1_xboole_0=C_97 | k1_xboole_0=B_96 | k1_xboole_0=A_95)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.50  tff(c_210, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_42, c_207])).
% 3.26/1.50  tff(c_213, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_210])).
% 3.26/1.50  tff(c_162, plain, (![A_72, B_73, C_74]: (r2_hidden(k1_mcart_1(A_72), B_73) | ~r2_hidden(A_72, k2_zfmisc_1(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.50  tff(c_246, plain, (![A_102, A_103, B_104, C_105]: (r2_hidden(k1_mcart_1(A_102), k2_zfmisc_1(A_103, B_104)) | ~r2_hidden(A_102, k3_zfmisc_1(A_103, B_104, C_105)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_162])).
% 3.26/1.50  tff(c_332, plain, (![A_121, A_122, B_123, C_124]: (r2_hidden(k1_mcart_1(A_121), k2_zfmisc_1(A_122, B_123)) | ~m1_subset_1(A_121, k3_zfmisc_1(A_122, B_123, C_124)))), inference(resolution, [status(thm)], [c_86, c_246])).
% 3.26/1.50  tff(c_338, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_332])).
% 3.26/1.50  tff(c_22, plain, (![A_17, B_18, C_19]: (r2_hidden(k1_mcart_1(A_17), B_18) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.50  tff(c_356, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_338, c_22])).
% 3.26/1.50  tff(c_366, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_356])).
% 3.26/1.50  tff(c_389, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_366, c_4])).
% 3.26/1.50  tff(c_251, plain, (![A_106, B_107, C_108, D_109]: (k6_mcart_1(A_106, B_107, C_108, D_109)=k2_mcart_1(k1_mcart_1(D_109)) | ~m1_subset_1(D_109, k3_zfmisc_1(A_106, B_107, C_108)) | k1_xboole_0=C_108 | k1_xboole_0=B_107 | k1_xboole_0=A_106)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.50  tff(c_254, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_42, c_251])).
% 3.26/1.50  tff(c_257, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_254])).
% 3.26/1.50  tff(c_20, plain, (![A_17, C_19, B_18]: (r2_hidden(k2_mcart_1(A_17), C_19) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.50  tff(c_358, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_338, c_20])).
% 3.26/1.50  tff(c_368, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_358])).
% 3.26/1.50  tff(c_403, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_368, c_4])).
% 3.26/1.50  tff(c_24, plain, (![A_20, B_21]: (k4_tarski(k1_mcart_1(A_20), k2_mcart_1(A_20))=A_20 | ~r2_hidden(A_20, B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.26/1.50  tff(c_354, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_338, c_24])).
% 3.26/1.50  tff(c_364, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_257, c_213, c_354])).
% 3.26/1.50  tff(c_16, plain, (![A_11, B_12, C_13]: (k4_tarski(k4_tarski(A_11, B_12), C_13)=k3_mcart_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.26/1.50  tff(c_423, plain, (![C_132]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_132)=k4_tarski(k1_mcart_1('#skF_5'), C_132))), inference(superposition, [status(thm), theory('equality')], [c_364, c_16])).
% 3.26/1.50  tff(c_40, plain, (![H_40, F_34, G_38]: (H_40='#skF_4' | k3_mcart_1(F_34, G_38, H_40)!='#skF_5' | ~m1_subset_1(H_40, '#skF_3') | ~m1_subset_1(G_38, '#skF_2') | ~m1_subset_1(F_34, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.26/1.50  tff(c_430, plain, (![C_132]: (C_132='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_132)!='#skF_5' | ~m1_subset_1(C_132, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_423, c_40])).
% 3.26/1.50  tff(c_439, plain, (![C_133]: (C_133='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_133)!='#skF_5' | ~m1_subset_1(C_133, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_403, c_430])).
% 3.26/1.50  tff(c_442, plain, (k2_mcart_1('#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_226, c_439])).
% 3.26/1.50  tff(c_445, plain, (k2_mcart_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_206, c_442])).
% 3.26/1.50  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_445])).
% 3.26/1.50  tff(c_448, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_66])).
% 3.26/1.50  tff(c_49, plain, (![A_44]: (k2_relat_1(A_44)=k1_xboole_0 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_45, c_2])).
% 3.26/1.50  tff(c_455, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_448, c_49])).
% 3.26/1.50  tff(c_534, plain, (![A_149, B_150, C_151]: (k2_zfmisc_1(k2_zfmisc_1(A_149, B_150), C_151)=k3_zfmisc_1(A_149, B_150, C_151))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.26/1.50  tff(c_552, plain, (![A_149, B_150, C_151]: (v1_relat_1(k3_zfmisc_1(A_149, B_150, C_151)))), inference(superposition, [status(thm), theory('equality')], [c_534, c_10])).
% 3.26/1.50  tff(c_571, plain, (![A_161, B_162]: (k4_tarski(k1_mcart_1(A_161), k2_mcart_1(A_161))=A_161 | ~r2_hidden(A_161, B_162) | ~v1_relat_1(B_162))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.26/1.50  tff(c_695, plain, (![A_199, B_200]: (k4_tarski(k1_mcart_1(A_199), k2_mcart_1(A_199))=A_199 | ~v1_relat_1(B_200) | v1_xboole_0(B_200) | ~m1_subset_1(A_199, B_200))), inference(resolution, [status(thm)], [c_6, c_571])).
% 3.26/1.50  tff(c_697, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_695])).
% 3.26/1.50  tff(c_700, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_552, c_697])).
% 3.26/1.50  tff(c_701, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_700])).
% 3.26/1.50  tff(c_709, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_701, c_2])).
% 3.26/1.50  tff(c_12, plain, (![A_9, B_10]: (k2_relat_1(k2_zfmisc_1(A_9, B_10))=B_10 | k1_xboole_0=B_10 | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.26/1.50  tff(c_543, plain, (![A_149, B_150, C_151]: (k2_relat_1(k3_zfmisc_1(A_149, B_150, C_151))=C_151 | k1_xboole_0=C_151 | k2_zfmisc_1(A_149, B_150)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_534, c_12])).
% 3.26/1.50  tff(c_716, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_709, c_543])).
% 3.26/1.50  tff(c_734, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_455, c_716])).
% 3.26/1.50  tff(c_735, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_734])).
% 3.26/1.50  tff(c_768, plain, (k2_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_735, c_12])).
% 3.26/1.50  tff(c_788, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_455, c_768])).
% 3.26/1.50  tff(c_790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_36, c_788])).
% 3.26/1.50  tff(c_792, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_700])).
% 3.26/1.50  tff(c_566, plain, (![A_157, C_158, A_159, B_160]: (r2_hidden(k2_mcart_1(A_157), C_158) | ~r2_hidden(A_157, k3_zfmisc_1(A_159, B_160, C_158)))), inference(superposition, [status(thm), theory('equality')], [c_534, c_20])).
% 3.26/1.50  tff(c_847, plain, (![A_217, C_218, A_219, B_220]: (r2_hidden(k2_mcart_1(A_217), C_218) | v1_xboole_0(k3_zfmisc_1(A_219, B_220, C_218)) | ~m1_subset_1(A_217, k3_zfmisc_1(A_219, B_220, C_218)))), inference(resolution, [status(thm)], [c_6, c_566])).
% 3.26/1.50  tff(c_851, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3') | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_847])).
% 3.26/1.50  tff(c_855, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_792, c_851])).
% 3.26/1.50  tff(c_862, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_855, c_4])).
% 3.26/1.50  tff(c_791, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_700])).
% 3.26/1.50  tff(c_591, plain, (![A_169, B_170, C_171, D_172]: (k5_mcart_1(A_169, B_170, C_171, D_172)=k1_mcart_1(k1_mcart_1(D_172)) | ~m1_subset_1(D_172, k3_zfmisc_1(A_169, B_170, C_171)) | k1_xboole_0=C_171 | k1_xboole_0=B_170 | k1_xboole_0=A_169)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.50  tff(c_594, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_42, c_591])).
% 3.26/1.50  tff(c_597, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_594])).
% 3.26/1.50  tff(c_496, plain, (![A_141, B_142, C_143]: (r2_hidden(k1_mcart_1(A_141), B_142) | ~r2_hidden(A_141, k2_zfmisc_1(B_142, C_143)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.50  tff(c_691, plain, (![A_196, B_197, C_198]: (r2_hidden(k1_mcart_1(A_196), B_197) | v1_xboole_0(k2_zfmisc_1(B_197, C_198)) | ~m1_subset_1(A_196, k2_zfmisc_1(B_197, C_198)))), inference(resolution, [status(thm)], [c_6, c_496])).
% 3.26/1.50  tff(c_693, plain, (![A_196, A_14, B_15, C_16]: (r2_hidden(k1_mcart_1(A_196), k2_zfmisc_1(A_14, B_15)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)) | ~m1_subset_1(A_196, k3_zfmisc_1(A_14, B_15, C_16)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_691])).
% 3.26/1.50  tff(c_867, plain, (![A_221, A_222, B_223, C_224]: (r2_hidden(k1_mcart_1(A_221), k2_zfmisc_1(A_222, B_223)) | v1_xboole_0(k3_zfmisc_1(A_222, B_223, C_224)) | ~m1_subset_1(A_221, k3_zfmisc_1(A_222, B_223, C_224)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_693])).
% 3.26/1.50  tff(c_871, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_867])).
% 3.26/1.50  tff(c_875, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_792, c_871])).
% 3.26/1.50  tff(c_879, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_875, c_22])).
% 3.26/1.50  tff(c_889, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_597, c_879])).
% 3.26/1.50  tff(c_912, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_889, c_4])).
% 3.26/1.50  tff(c_650, plain, (![A_185, B_186, C_187, D_188]: (k6_mcart_1(A_185, B_186, C_187, D_188)=k2_mcart_1(k1_mcart_1(D_188)) | ~m1_subset_1(D_188, k3_zfmisc_1(A_185, B_186, C_187)) | k1_xboole_0=C_187 | k1_xboole_0=B_186 | k1_xboole_0=A_185)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.26/1.50  tff(c_656, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_42, c_650])).
% 3.26/1.50  tff(c_659, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_656])).
% 3.26/1.50  tff(c_881, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_875, c_20])).
% 3.26/1.50  tff(c_891, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_659, c_881])).
% 3.26/1.50  tff(c_919, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_891, c_4])).
% 3.26/1.50  tff(c_877, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_875, c_24])).
% 3.26/1.50  tff(c_887, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_597, c_659, c_877])).
% 3.26/1.50  tff(c_938, plain, (![C_225]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_225)=k4_tarski(k1_mcart_1('#skF_5'), C_225))), inference(superposition, [status(thm), theory('equality')], [c_887, c_16])).
% 3.26/1.50  tff(c_945, plain, (![C_225]: (C_225='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_225)!='#skF_5' | ~m1_subset_1(C_225, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_938, c_40])).
% 3.26/1.50  tff(c_954, plain, (![C_226]: (C_226='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_226)!='#skF_5' | ~m1_subset_1(C_226, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_912, c_919, c_945])).
% 3.26/1.50  tff(c_957, plain, (k2_mcart_1('#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_791, c_954])).
% 3.26/1.50  tff(c_960, plain, (k2_mcart_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_862, c_957])).
% 3.26/1.50  tff(c_962, plain, $false, inference(negUnitSimplification, [status(thm)], [c_582, c_960])).
% 3.26/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.50  
% 3.26/1.50  Inference rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Ref     : 0
% 3.26/1.50  #Sup     : 233
% 3.26/1.50  #Fact    : 0
% 3.26/1.50  #Define  : 0
% 3.26/1.50  #Split   : 6
% 3.26/1.50  #Chain   : 0
% 3.26/1.50  #Close   : 0
% 3.26/1.50  
% 3.26/1.50  Ordering : KBO
% 3.26/1.50  
% 3.26/1.50  Simplification rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Subsume      : 36
% 3.26/1.50  #Demod        : 101
% 3.26/1.50  #Tautology    : 95
% 3.26/1.50  #SimpNegUnit  : 19
% 3.26/1.50  #BackRed      : 4
% 3.26/1.50  
% 3.26/1.50  #Partial instantiations: 0
% 3.26/1.50  #Strategies tried      : 1
% 3.26/1.50  
% 3.26/1.50  Timing (in seconds)
% 3.26/1.50  ----------------------
% 3.26/1.50  Preprocessing        : 0.33
% 3.26/1.50  Parsing              : 0.18
% 3.26/1.50  CNF conversion       : 0.02
% 3.26/1.50  Main loop            : 0.41
% 3.26/1.50  Inferencing          : 0.16
% 3.26/1.50  Reduction            : 0.12
% 3.26/1.50  Demodulation         : 0.08
% 3.26/1.50  BG Simplification    : 0.02
% 3.26/1.50  Subsumption          : 0.07
% 3.26/1.50  Abstraction          : 0.02
% 3.26/1.50  MUC search           : 0.00
% 3.26/1.50  Cooper               : 0.00
% 3.26/1.50  Total                : 0.79
% 3.26/1.50  Index Insertion      : 0.00
% 3.26/1.50  Index Deletion       : 0.00
% 3.26/1.50  Index Matching       : 0.00
% 3.26/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
