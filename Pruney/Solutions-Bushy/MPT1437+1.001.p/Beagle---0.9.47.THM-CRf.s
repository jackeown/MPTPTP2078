%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1437+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:56 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 366 expanded)
%              Number of leaves         :   31 ( 138 expanded)
%              Depth                    :   18
%              Number of atoms          :  213 (1332 expanded)
%              Number of equality atoms :   34 ( 146 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > v10_lattices > l3_lattices > l2_lattices > l1_struct_0 > l1_lattices > k1_domain_1 > k4_tarski > #nlpp > u1_struct_0 > k8_filter_1 > a_1_0_filter_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_105,negated_conjecture,(
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

tff(f_33,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => k8_filter_1(A) = a_1_0_filter_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_filter_1)).

tff(f_69,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_lattices(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_lattices)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(C,A)
        & m1_subset_1(D,B) )
     => k1_domain_1(A,B,C,D) = k4_tarski(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_domain_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( k4_tarski(A,B) = k4_tarski(C,D)
     => ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_67,plain,(
    ! [A_37] :
      ( k8_filter_1(A_37) = a_1_0_filter_1(A_37)
      | ~ l3_lattices(A_37)
      | ~ v10_lattices(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,
    ( k8_filter_1('#skF_3') = a_1_0_filter_1('#skF_3')
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_36])).

tff(c_73,plain,(
    k8_filter_1('#skF_3') = a_1_0_filter_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_70])).

tff(c_38,plain,
    ( ~ r3_lattices('#skF_3','#skF_4','#skF_5')
    | ~ r2_hidden(k1_domain_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),k8_filter_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_78,plain,
    ( ~ r3_lattices('#skF_3','#skF_4','#skF_5')
    | ~ r2_hidden(k1_domain_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),a_1_0_filter_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_38])).

tff(c_79,plain,(
    ~ r2_hidden(k1_domain_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),a_1_0_filter_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_44,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),k8_filter_1('#skF_3'))
    | r3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_80,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),a_1_0_filter_1('#skF_3'))
    | r3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_44])).

tff(c_81,plain,(
    r3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_80])).

tff(c_148,plain,(
    ! [B_54,C_55,D_56] :
      ( r2_hidden(k1_domain_1(u1_struct_0(B_54),u1_struct_0(B_54),C_55,D_56),a_1_0_filter_1(B_54))
      | ~ r3_lattices(B_54,C_55,D_56)
      | ~ m1_subset_1(D_56,u1_struct_0(B_54))
      | ~ m1_subset_1(C_55,u1_struct_0(B_54))
      | ~ l3_lattices(B_54)
      | ~ v10_lattices(B_54)
      | v2_struct_0(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_151,plain,
    ( ~ r3_lattices('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_79])).

tff(c_165,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_81,c_151])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_165])).

tff(c_168,plain,(
    ~ r3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_46,plain,(
    ! [A_26] :
      ( l1_lattices(A_26)
      | ~ l3_lattices(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    l1_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_lattices(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_174,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k1_domain_1(A_61,B_62,C_63,D_64) = k4_tarski(C_63,D_64)
      | ~ m1_subset_1(D_64,B_62)
      | ~ m1_subset_1(C_63,A_61)
      | v1_xboole_0(B_62)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_185,plain,(
    ! [A_61,C_63] :
      ( k1_domain_1(A_61,u1_struct_0('#skF_3'),C_63,'#skF_4') = k4_tarski(C_63,'#skF_4')
      | ~ m1_subset_1(C_63,A_61)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_30,c_174])).

tff(c_187,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_10,plain,(
    ! [A_4] :
      ( ~ v1_xboole_0(u1_struct_0(A_4))
      | ~ l1_struct_0(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_190,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_10])).

tff(c_193,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_190])).

tff(c_196,plain,(
    ~ l1_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_193])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_196])).

tff(c_202,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_186,plain,(
    ! [A_61,C_63] :
      ( k1_domain_1(A_61,u1_struct_0('#skF_3'),C_63,'#skF_5') = k4_tarski(C_63,'#skF_5')
      | ~ m1_subset_1(C_63,A_61)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_28,c_174])).

tff(c_213,plain,(
    ! [A_67,C_68] :
      ( k1_domain_1(A_67,u1_struct_0('#skF_3'),C_68,'#skF_5') = k4_tarski(C_68,'#skF_5')
      | ~ m1_subset_1(C_68,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_186])).

tff(c_169,plain,(
    r2_hidden(k1_domain_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),'#skF_4','#skF_5'),a_1_0_filter_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_219,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_5'),a_1_0_filter_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_169])).

tff(c_225,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_5'),a_1_0_filter_1('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_219])).

tff(c_226,plain,(
    r2_hidden(k4_tarski('#skF_4','#skF_5'),a_1_0_filter_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_225])).

tff(c_20,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1('#skF_1'(A_5,B_6),u1_struct_0(B_6))
      | ~ r2_hidden(A_5,a_1_0_filter_1(B_6))
      | ~ l3_lattices(B_6)
      | ~ v10_lattices(B_6)
      | v2_struct_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [B_6,A_5] :
      ( k1_domain_1(u1_struct_0(B_6),u1_struct_0(B_6),'#skF_1'(A_5,B_6),'#skF_2'(A_5,B_6)) = A_5
      | ~ r2_hidden(A_5,a_1_0_filter_1(B_6))
      | ~ l3_lattices(B_6)
      | ~ v10_lattices(B_6)
      | v2_struct_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1('#skF_2'(A_5,B_6),u1_struct_0(B_6))
      | ~ r2_hidden(A_5,a_1_0_filter_1(B_6))
      | ~ l3_lattices(B_6)
      | ~ v10_lattices(B_6)
      | v2_struct_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_258,plain,(
    ! [A_78,B_79,C_80,A_81] :
      ( k1_domain_1(A_78,u1_struct_0(B_79),C_80,'#skF_2'(A_81,B_79)) = k4_tarski(C_80,'#skF_2'(A_81,B_79))
      | ~ m1_subset_1(C_80,A_78)
      | v1_xboole_0(u1_struct_0(B_79))
      | v1_xboole_0(A_78)
      | ~ r2_hidden(A_81,a_1_0_filter_1(B_79))
      | ~ l3_lattices(B_79)
      | ~ v10_lattices(B_79)
      | v2_struct_0(B_79) ) ),
    inference(resolution,[status(thm)],[c_18,c_174])).

tff(c_291,plain,(
    ! [A_86,B_87] :
      ( k4_tarski('#skF_1'(A_86,B_87),'#skF_2'(A_86,B_87)) = A_86
      | ~ m1_subset_1('#skF_1'(A_86,B_87),u1_struct_0(B_87))
      | v1_xboole_0(u1_struct_0(B_87))
      | v1_xboole_0(u1_struct_0(B_87))
      | ~ r2_hidden(A_86,a_1_0_filter_1(B_87))
      | ~ l3_lattices(B_87)
      | ~ v10_lattices(B_87)
      | v2_struct_0(B_87)
      | ~ r2_hidden(A_86,a_1_0_filter_1(B_87))
      | ~ l3_lattices(B_87)
      | ~ v10_lattices(B_87)
      | v2_struct_0(B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_258])).

tff(c_295,plain,(
    ! [A_88,B_89] :
      ( k4_tarski('#skF_1'(A_88,B_89),'#skF_2'(A_88,B_89)) = A_88
      | v1_xboole_0(u1_struct_0(B_89))
      | ~ r2_hidden(A_88,a_1_0_filter_1(B_89))
      | ~ l3_lattices(B_89)
      | ~ v10_lattices(B_89)
      | v2_struct_0(B_89) ) ),
    inference(resolution,[status(thm)],[c_20,c_291])).

tff(c_26,plain,(
    ! [C_19,A_17,D_20,B_18] :
      ( C_19 = A_17
      | k4_tarski(C_19,D_20) != k4_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_310,plain,(
    ! [C_19,A_88,B_89,D_20] :
      ( C_19 = '#skF_1'(A_88,B_89)
      | k4_tarski(C_19,D_20) != A_88
      | v1_xboole_0(u1_struct_0(B_89))
      | ~ r2_hidden(A_88,a_1_0_filter_1(B_89))
      | ~ l3_lattices(B_89)
      | ~ v10_lattices(B_89)
      | v2_struct_0(B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_26])).

tff(c_332,plain,(
    ! [C_98,D_99,B_100] :
      ( '#skF_1'(k4_tarski(C_98,D_99),B_100) = C_98
      | v1_xboole_0(u1_struct_0(B_100))
      | ~ r2_hidden(k4_tarski(C_98,D_99),a_1_0_filter_1(B_100))
      | ~ l3_lattices(B_100)
      | ~ v10_lattices(B_100)
      | v2_struct_0(B_100) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_310])).

tff(c_344,plain,
    ( '#skF_1'(k4_tarski('#skF_4','#skF_5'),'#skF_3') = '#skF_4'
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_226,c_332])).

tff(c_355,plain,
    ( '#skF_1'(k4_tarski('#skF_4','#skF_5'),'#skF_3') = '#skF_4'
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_344])).

tff(c_356,plain,(
    '#skF_1'(k4_tarski('#skF_4','#skF_5'),'#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_202,c_355])).

tff(c_294,plain,(
    ! [A_5,B_6] :
      ( k4_tarski('#skF_1'(A_5,B_6),'#skF_2'(A_5,B_6)) = A_5
      | v1_xboole_0(u1_struct_0(B_6))
      | ~ r2_hidden(A_5,a_1_0_filter_1(B_6))
      | ~ l3_lattices(B_6)
      | ~ v10_lattices(B_6)
      | v2_struct_0(B_6) ) ),
    inference(resolution,[status(thm)],[c_20,c_291])).

tff(c_360,plain,
    ( k4_tarski('#skF_4','#skF_2'(k4_tarski('#skF_4','#skF_5'),'#skF_3')) = k4_tarski('#skF_4','#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ r2_hidden(k4_tarski('#skF_4','#skF_5'),a_1_0_filter_1('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_294])).

tff(c_376,plain,
    ( k4_tarski('#skF_4','#skF_2'(k4_tarski('#skF_4','#skF_5'),'#skF_3')) = k4_tarski('#skF_4','#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_226,c_360])).

tff(c_377,plain,(
    k4_tarski('#skF_4','#skF_2'(k4_tarski('#skF_4','#skF_5'),'#skF_3')) = k4_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_202,c_376])).

tff(c_24,plain,(
    ! [D_20,B_18,C_19,A_17] :
      ( D_20 = B_18
      | k4_tarski(C_19,D_20) != k4_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_401,plain,(
    ! [B_18,A_17] :
      ( B_18 = '#skF_2'(k4_tarski('#skF_4','#skF_5'),'#skF_3')
      | k4_tarski(A_17,B_18) != k4_tarski('#skF_4','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_24])).

tff(c_417,plain,(
    '#skF_2'(k4_tarski('#skF_4','#skF_5'),'#skF_3') = '#skF_5' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_401])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( r3_lattices(B_6,'#skF_1'(A_5,B_6),'#skF_2'(A_5,B_6))
      | ~ r2_hidden(A_5,a_1_0_filter_1(B_6))
      | ~ l3_lattices(B_6)
      | ~ v10_lattices(B_6)
      | v2_struct_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_369,plain,
    ( r3_lattices('#skF_3','#skF_4','#skF_2'(k4_tarski('#skF_4','#skF_5'),'#skF_3'))
    | ~ r2_hidden(k4_tarski('#skF_4','#skF_5'),a_1_0_filter_1('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_14])).

tff(c_385,plain,
    ( r3_lattices('#skF_3','#skF_4','#skF_2'(k4_tarski('#skF_4','#skF_5'),'#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_226,c_369])).

tff(c_386,plain,(
    r3_lattices('#skF_3','#skF_4','#skF_2'(k4_tarski('#skF_4','#skF_5'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_385])).

tff(c_427,plain,(
    r3_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_386])).

tff(c_429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_427])).

%------------------------------------------------------------------------------
