%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1839+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:30 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 326 expanded)
%              Number of leaves         :   29 ( 120 expanded)
%              Depth                    :   24
%              Number of atoms          :  160 ( 748 expanded)
%              Number of equality atoms :   30 ( 145 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_7] :
      ( v1_xboole_0(A_7)
      | r2_hidden('#skF_2'(A_7),A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_168,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_180,plain,(
    ! [B_67,A_68,A_69] :
      ( ~ v1_xboole_0(B_67)
      | ~ r2_hidden(A_68,A_69)
      | ~ r1_tarski(A_69,B_67) ) ),
    inference(resolution,[status(thm)],[c_32,c_168])).

tff(c_199,plain,(
    ! [B_73,A_74] :
      ( ~ v1_xboole_0(B_73)
      | ~ r1_tarski(A_74,B_73)
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_12,c_180])).

tff(c_227,plain,(
    ! [A_77,B_78] :
      ( ~ v1_xboole_0(A_77)
      | v1_xboole_0(k3_xboole_0(A_77,B_78)) ) ),
    inference(resolution,[status(thm)],[c_18,c_199])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_40,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_45,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_237,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_227,c_45])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_101,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(A_43,B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,(
    ! [A_7] :
      ( m1_subset_1('#skF_2'(A_7),A_7)
      | v1_xboole_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_53,plain,(
    ! [B_39,A_40] : k3_xboole_0(B_39,A_40) = k3_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_68,plain,(
    ! [B_39,A_40] : r1_tarski(k3_xboole_0(B_39,A_40),A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_18])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_187,plain,(
    ! [A_70,C_71,B_72] :
      ( m1_subset_1(A_70,C_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(C_71))
      | ~ r2_hidden(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_238,plain,(
    ! [A_79,B_80,A_81] :
      ( m1_subset_1(A_79,B_80)
      | ~ r2_hidden(A_79,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_32,c_187])).

tff(c_414,plain,(
    ! [A_107,B_108,B_109] :
      ( m1_subset_1(A_107,B_108)
      | ~ r1_tarski(B_109,B_108)
      | v1_xboole_0(B_109)
      | ~ m1_subset_1(A_107,B_109) ) ),
    inference(resolution,[status(thm)],[c_24,c_238])).

tff(c_671,plain,(
    ! [A_128,A_129,B_130] :
      ( m1_subset_1(A_128,A_129)
      | v1_xboole_0(k3_xboole_0(B_130,A_129))
      | ~ m1_subset_1(A_128,k3_xboole_0(B_130,A_129)) ) ),
    inference(resolution,[status(thm)],[c_68,c_414])).

tff(c_703,plain,(
    ! [B_131,A_132] :
      ( m1_subset_1('#skF_2'(k3_xboole_0(B_131,A_132)),A_132)
      | v1_xboole_0(k3_xboole_0(B_131,A_132)) ) ),
    inference(resolution,[status(thm)],[c_105,c_671])).

tff(c_734,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1('#skF_2'(k3_xboole_0(B_2,A_1)),B_2)
      | v1_xboole_0(k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_703])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6,plain,(
    ! [A_3] :
      ( k6_domain_1(A_3,'#skF_1'(A_3)) = A_3
      | ~ v1_zfmisc_1(A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_1'(A_3),A_3)
      | ~ v1_zfmisc_1(A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_275,plain,(
    ! [A_86,B_87] :
      ( k6_domain_1(A_86,B_87) = k1_tarski(B_87)
      | ~ m1_subset_1(B_87,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_382,plain,(
    ! [A_104] :
      ( k6_domain_1(A_104,'#skF_1'(A_104)) = k1_tarski('#skF_1'(A_104))
      | ~ v1_zfmisc_1(A_104)
      | v1_xboole_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_8,c_275])).

tff(c_519,plain,(
    ! [A_114] :
      ( k1_tarski('#skF_1'(A_114)) = A_114
      | ~ v1_zfmisc_1(A_114)
      | v1_xboole_0(A_114)
      | ~ v1_zfmisc_1(A_114)
      | v1_xboole_0(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_382])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_tarski(A_23),B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_115,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(k1_tarski(A_53),k1_tarski(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_120,plain,(
    ! [B_52,A_23] :
      ( B_52 = A_23
      | ~ r2_hidden(A_23,k1_tarski(B_52)) ) ),
    inference(resolution,[status(thm)],[c_28,c_115])).

tff(c_1592,plain,(
    ! [A_196,A_197] :
      ( A_196 = '#skF_1'(A_197)
      | ~ r2_hidden(A_196,A_197)
      | ~ v1_zfmisc_1(A_197)
      | v1_xboole_0(A_197)
      | ~ v1_zfmisc_1(A_197)
      | v1_xboole_0(A_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_120])).

tff(c_1634,plain,(
    ! [A_200] :
      ( '#skF_2'(A_200) = '#skF_1'(A_200)
      | ~ v1_zfmisc_1(A_200)
      | v1_xboole_0(A_200) ) ),
    inference(resolution,[status(thm)],[c_12,c_1592])).

tff(c_1637,plain,
    ( '#skF_2'('#skF_3') = '#skF_1'('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1634])).

tff(c_1640,plain,(
    '#skF_2'('#skF_3') = '#skF_1'('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1637])).

tff(c_291,plain,(
    ! [A_7] :
      ( k6_domain_1(A_7,'#skF_2'(A_7)) = k1_tarski('#skF_2'(A_7))
      | v1_xboole_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_105,c_275])).

tff(c_1669,plain,
    ( k6_domain_1('#skF_3','#skF_1'('#skF_3')) = k1_tarski('#skF_2'('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1640,c_291])).

tff(c_1695,plain,
    ( k6_domain_1('#skF_3','#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1640,c_1669])).

tff(c_1696,plain,(
    k6_domain_1('#skF_3','#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1695])).

tff(c_1817,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1696,c_6])).

tff(c_1846,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1817])).

tff(c_1847,plain,(
    k1_tarski('#skF_1'('#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1846])).

tff(c_138,plain,(
    ! [A_59,B_60] :
      ( r2_hidden(A_59,B_60)
      | v1_xboole_0(B_60)
      | ~ m1_subset_1(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_149,plain,(
    ! [B_52,A_59] :
      ( B_52 = A_59
      | v1_xboole_0(k1_tarski(B_52))
      | ~ m1_subset_1(A_59,k1_tarski(B_52)) ) ),
    inference(resolution,[status(thm)],[c_138,c_120])).

tff(c_1888,plain,(
    ! [A_59] :
      ( A_59 = '#skF_1'('#skF_3')
      | v1_xboole_0(k1_tarski('#skF_1'('#skF_3')))
      | ~ m1_subset_1(A_59,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1847,c_149])).

tff(c_1939,plain,(
    ! [A_59] :
      ( A_59 = '#skF_1'('#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_59,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_1888])).

tff(c_2105,plain,(
    ! [A_205] :
      ( A_205 = '#skF_1'('#skF_3')
      | ~ m1_subset_1(A_205,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1939])).

tff(c_2867,plain,(
    ! [A_229] :
      ( '#skF_2'(k3_xboole_0('#skF_3',A_229)) = '#skF_1'('#skF_3')
      | v1_xboole_0(k3_xboole_0(A_229,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_734,c_2105])).

tff(c_2870,plain,(
    '#skF_2'(k3_xboole_0('#skF_3','#skF_4')) = '#skF_1'('#skF_3') ),
    inference(resolution,[status(thm)],[c_2867,c_45])).

tff(c_2880,plain,(
    '#skF_2'(k3_xboole_0('#skF_4','#skF_3')) = '#skF_1'('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2870])).

tff(c_2898,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2880,c_734])).

tff(c_2941,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2898])).

tff(c_2942,plain,(
    m1_subset_1('#skF_1'('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_2941])).

tff(c_2387,plain,(
    ! [B_212] :
      ( r1_tarski('#skF_3',B_212)
      | ~ r2_hidden('#skF_1'('#skF_3'),B_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1847,c_28])).

tff(c_2409,plain,(
    ! [B_22] :
      ( r1_tarski('#skF_3',B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1('#skF_1'('#skF_3'),B_22) ) ),
    inference(resolution,[status(thm)],[c_24,c_2387])).

tff(c_2964,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2942,c_2409])).

tff(c_2977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_38,c_2964])).

%------------------------------------------------------------------------------
