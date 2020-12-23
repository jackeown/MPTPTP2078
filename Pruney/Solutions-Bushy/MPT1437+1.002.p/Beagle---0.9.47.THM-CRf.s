%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1437+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:56 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 339 expanded)
%              Number of leaves         :   37 ( 132 expanded)
%              Depth                    :   17
%              Number of atoms          :  219 (1213 expanded)
%              Number of equality atoms :   37 ( 134 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v1_xboole_0 > v10_lattices > l3_lattices > l2_lattices > l1_struct_0 > l1_lattices > k1_domain_1 > k4_tarski > #nlpp > u1_struct_0 > k8_filter_1 > a_1_0_filter_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_domain_1,type,(
    k1_domain_1: ( $i * $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(a_1_0_filter_1,type,(
    a_1_0_filter_1: $i > $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k8_filter_1,type,(
    k8_filter_1: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(k1_domain_1(u1_struct_0(A),u1_struct_0(A),B,C),k8_filter_1(A))
                <=> r3_lattices(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_filter_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_1_0_filter_1(B))
      <=> ? [C,D] :
            ( m1_subset_1(C,u1_struct_0(B))
            & m1_subset_1(D,u1_struct_0(B))
            & A = k1_domain_1(u1_struct_0(B),u1_struct_0(B),C,D)
            & r3_lattices(B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_1_0_filter_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => k8_filter_1(A) = a_1_0_filter_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_filter_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_59,axiom,(
    ! [A] :
      ( l2_lattices(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l2_lattices)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(C,A)
        & m1_subset_1(D,B) )
     => k1_domain_1(A,B,C,D) = k4_tarski(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_domain_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( k4_tarski(A,B) = k4_tarski(C,D)
     => ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_54,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_52,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_64,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),k8_filter_1('#skF_3'))
    | r3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_76,plain,(
    r3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_308,plain,(
    ! [B_83,C_84,D_85] :
      ( r2_hidden(k1_domain_1(u1_struct_0(B_83),u1_struct_0(B_83),C_84,D_85),a_1_0_filter_1(B_83))
      | ~ r3_lattices(B_83,C_84,D_85)
      | ~ m1_subset_1(D_85,u1_struct_0(B_83))
      | ~ m1_subset_1(C_84,u1_struct_0(B_83))
      | ~ l3_lattices(B_83)
      | ~ v10_lattices(B_83)
      | v2_struct_0(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_110,plain,(
    ! [A_55] :
      ( k8_filter_1(A_55) = a_1_0_filter_1(A_55)
      | ~ l3_lattices(A_55)
      | ~ v10_lattices(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_113,plain,
    ( k8_filter_1('#skF_3') = a_1_0_filter_1('#skF_3')
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_56])).

tff(c_116,plain,(
    k8_filter_1('#skF_3') = a_1_0_filter_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_113])).

tff(c_58,plain,
    ( ~ r3_lattices('#skF_3','#skF_4','#skF_5')
    | ~ r2_hidden(k1_domain_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),k8_filter_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_96,plain,(
    ~ r2_hidden(k1_domain_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),k8_filter_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_58])).

tff(c_117,plain,(
    ~ r2_hidden(k1_domain_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),a_1_0_filter_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_96])).

tff(c_311,plain,
    ( ~ r3_lattices('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_308,c_117])).

tff(c_328,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_76,c_311])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_328])).

tff(c_332,plain,(
    ~ r3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_71,plain,(
    ! [A_35] :
      ( l2_lattices(A_35)
      | ~ l3_lattices(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_75,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_71])).

tff(c_18,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l2_lattices(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_336,plain,(
    l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_18])).

tff(c_383,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k1_domain_1(A_110,B_111,C_112,D_113) = k4_tarski(C_112,D_113)
      | ~ m1_subset_1(D_113,B_111)
      | ~ m1_subset_1(C_112,A_110)
      | v1_xboole_0(B_111)
      | v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_394,plain,(
    ! [A_110,C_112] :
      ( k1_domain_1(A_110,u1_struct_0('#skF_3'),C_112,'#skF_4') = k4_tarski(C_112,'#skF_4')
      | ~ m1_subset_1(C_112,A_110)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_50,c_383])).

tff(c_396,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_24,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_399,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_396,c_24])).

tff(c_402,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_399])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_402])).

tff(c_406,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_395,plain,(
    ! [A_110,C_112] :
      ( k1_domain_1(A_110,u1_struct_0('#skF_3'),C_112,'#skF_5') = k4_tarski(C_112,'#skF_5')
      | ~ m1_subset_1(C_112,A_110)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_48,c_383])).

tff(c_417,plain,(
    ! [A_116,C_117] :
      ( k1_domain_1(A_116,u1_struct_0('#skF_3'),C_117,'#skF_5') = k4_tarski(C_117,'#skF_5')
      | ~ m1_subset_1(C_117,A_116)
      | v1_xboole_0(A_116) ) ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_395])).

tff(c_364,plain,(
    ! [A_105] :
      ( k8_filter_1(A_105) = a_1_0_filter_1(A_105)
      | ~ l3_lattices(A_105)
      | ~ v10_lattices(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_367,plain,
    ( k8_filter_1('#skF_3') = a_1_0_filter_1('#skF_3')
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_364,c_56])).

tff(c_370,plain,(
    k8_filter_1('#skF_3') = a_1_0_filter_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_367])).

tff(c_331,plain,(
    r2_hidden(k1_domain_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),k8_filter_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_372,plain,(
    r2_hidden(k1_domain_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),a_1_0_filter_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_331])).

tff(c_423,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_5'),a_1_0_filter_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_372])).

tff(c_429,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_5'),a_1_0_filter_1('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_423])).

tff(c_430,plain,(
    r2_hidden(k4_tarski('#skF_4','#skF_5'),a_1_0_filter_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_429])).

tff(c_34,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1('#skF_1'(A_6,B_7),u1_struct_0(B_7))
      | ~ r2_hidden(A_6,a_1_0_filter_1(B_7))
      | ~ l3_lattices(B_7)
      | ~ v10_lattices(B_7)
      | v2_struct_0(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    ! [B_7,A_6] :
      ( k1_domain_1(u1_struct_0(B_7),u1_struct_0(B_7),'#skF_1'(A_6,B_7),'#skF_2'(A_6,B_7)) = A_6
      | ~ r2_hidden(A_6,a_1_0_filter_1(B_7))
      | ~ l3_lattices(B_7)
      | ~ v10_lattices(B_7)
      | v2_struct_0(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1('#skF_2'(A_6,B_7),u1_struct_0(B_7))
      | ~ r2_hidden(A_6,a_1_0_filter_1(B_7))
      | ~ l3_lattices(B_7)
      | ~ v10_lattices(B_7)
      | v2_struct_0(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_620,plain,(
    ! [A_141,B_142,C_143,A_144] :
      ( k1_domain_1(A_141,u1_struct_0(B_142),C_143,'#skF_2'(A_144,B_142)) = k4_tarski(C_143,'#skF_2'(A_144,B_142))
      | ~ m1_subset_1(C_143,A_141)
      | v1_xboole_0(u1_struct_0(B_142))
      | v1_xboole_0(A_141)
      | ~ r2_hidden(A_144,a_1_0_filter_1(B_142))
      | ~ l3_lattices(B_142)
      | ~ v10_lattices(B_142)
      | v2_struct_0(B_142) ) ),
    inference(resolution,[status(thm)],[c_32,c_383])).

tff(c_775,plain,(
    ! [A_169,B_170] :
      ( k4_tarski('#skF_1'(A_169,B_170),'#skF_2'(A_169,B_170)) = A_169
      | ~ m1_subset_1('#skF_1'(A_169,B_170),u1_struct_0(B_170))
      | v1_xboole_0(u1_struct_0(B_170))
      | v1_xboole_0(u1_struct_0(B_170))
      | ~ r2_hidden(A_169,a_1_0_filter_1(B_170))
      | ~ l3_lattices(B_170)
      | ~ v10_lattices(B_170)
      | v2_struct_0(B_170)
      | ~ r2_hidden(A_169,a_1_0_filter_1(B_170))
      | ~ l3_lattices(B_170)
      | ~ v10_lattices(B_170)
      | v2_struct_0(B_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_620])).

tff(c_779,plain,(
    ! [A_171,B_172] :
      ( k4_tarski('#skF_1'(A_171,B_172),'#skF_2'(A_171,B_172)) = A_171
      | v1_xboole_0(u1_struct_0(B_172))
      | ~ r2_hidden(A_171,a_1_0_filter_1(B_172))
      | ~ l3_lattices(B_172)
      | ~ v10_lattices(B_172)
      | v2_struct_0(B_172) ) ),
    inference(resolution,[status(thm)],[c_34,c_775])).

tff(c_42,plain,(
    ! [D_26,B_24,C_25,A_23] :
      ( D_26 = B_24
      | k4_tarski(C_25,D_26) != k4_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_791,plain,(
    ! [B_24,A_171,B_172,A_23] :
      ( B_24 = '#skF_2'(A_171,B_172)
      | k4_tarski(A_23,B_24) != A_171
      | v1_xboole_0(u1_struct_0(B_172))
      | ~ r2_hidden(A_171,a_1_0_filter_1(B_172))
      | ~ l3_lattices(B_172)
      | ~ v10_lattices(B_172)
      | v2_struct_0(B_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_42])).

tff(c_816,plain,(
    ! [A_181,B_182,B_183] :
      ( '#skF_2'(k4_tarski(A_181,B_182),B_183) = B_182
      | v1_xboole_0(u1_struct_0(B_183))
      | ~ r2_hidden(k4_tarski(A_181,B_182),a_1_0_filter_1(B_183))
      | ~ l3_lattices(B_183)
      | ~ v10_lattices(B_183)
      | v2_struct_0(B_183) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_791])).

tff(c_828,plain,
    ( '#skF_2'(k4_tarski('#skF_4','#skF_5'),'#skF_3') = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_430,c_816])).

tff(c_842,plain,
    ( '#skF_2'(k4_tarski('#skF_4','#skF_5'),'#skF_3') = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_828])).

tff(c_843,plain,(
    '#skF_2'(k4_tarski('#skF_4','#skF_5'),'#skF_3') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_406,c_842])).

tff(c_778,plain,(
    ! [A_6,B_7] :
      ( k4_tarski('#skF_1'(A_6,B_7),'#skF_2'(A_6,B_7)) = A_6
      | v1_xboole_0(u1_struct_0(B_7))
      | ~ r2_hidden(A_6,a_1_0_filter_1(B_7))
      | ~ l3_lattices(B_7)
      | ~ v10_lattices(B_7)
      | v2_struct_0(B_7) ) ),
    inference(resolution,[status(thm)],[c_34,c_775])).

tff(c_848,plain,
    ( k4_tarski('#skF_1'(k4_tarski('#skF_4','#skF_5'),'#skF_3'),'#skF_5') = k4_tarski('#skF_4','#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ r2_hidden(k4_tarski('#skF_4','#skF_5'),a_1_0_filter_1('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_778])).

tff(c_870,plain,
    ( k4_tarski('#skF_1'(k4_tarski('#skF_4','#skF_5'),'#skF_3'),'#skF_5') = k4_tarski('#skF_4','#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_430,c_848])).

tff(c_871,plain,(
    k4_tarski('#skF_1'(k4_tarski('#skF_4','#skF_5'),'#skF_3'),'#skF_5') = k4_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_406,c_870])).

tff(c_44,plain,(
    ! [C_25,A_23,D_26,B_24] :
      ( C_25 = A_23
      | k4_tarski(C_25,D_26) != k4_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_920,plain,(
    ! [A_23,B_24] :
      ( A_23 = '#skF_1'(k4_tarski('#skF_4','#skF_5'),'#skF_3')
      | k4_tarski(A_23,B_24) != k4_tarski('#skF_4','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_44])).

tff(c_938,plain,(
    '#skF_1'(k4_tarski('#skF_4','#skF_5'),'#skF_3') = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_920])).

tff(c_28,plain,(
    ! [B_7,A_6] :
      ( r3_lattices(B_7,'#skF_1'(A_6,B_7),'#skF_2'(A_6,B_7))
      | ~ r2_hidden(A_6,a_1_0_filter_1(B_7))
      | ~ l3_lattices(B_7)
      | ~ v10_lattices(B_7)
      | v2_struct_0(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_863,plain,
    ( r3_lattices('#skF_3','#skF_1'(k4_tarski('#skF_4','#skF_5'),'#skF_3'),'#skF_5')
    | ~ r2_hidden(k4_tarski('#skF_4','#skF_5'),a_1_0_filter_1('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_28])).

tff(c_883,plain,
    ( r3_lattices('#skF_3','#skF_1'(k4_tarski('#skF_4','#skF_5'),'#skF_3'),'#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_430,c_863])).

tff(c_884,plain,(
    r3_lattices('#skF_3','#skF_1'(k4_tarski('#skF_4','#skF_5'),'#skF_3'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_883])).

tff(c_963,plain,(
    r3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_884])).

tff(c_965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_963])).

%------------------------------------------------------------------------------
