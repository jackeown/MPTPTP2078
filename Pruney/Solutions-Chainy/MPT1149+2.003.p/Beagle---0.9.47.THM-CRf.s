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
% DateTime   : Thu Dec  3 10:19:23 EST 2020

% Result     : Theorem 7.09s
% Output     : CNFRefutation 7.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 609 expanded)
%              Number of leaves         :   37 ( 239 expanded)
%              Depth                    :   25
%              Number of atoms          :  356 (2007 expanded)
%              Number of equality atoms :   25 ( 216 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k1_struct_0(A)) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_orders_2)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,B)
               => r2_hidden(D,C) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_161,plain,(
    ! [A_76,B_77] :
      ( k1_orders_2(A_76,B_77) = a_2_0_orders_2(A_76,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | ~ v5_orders_2(A_76)
      | ~ v4_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_280,plain,(
    ! [A_88] :
      ( k1_orders_2(A_88,k1_xboole_0) = a_2_0_orders_2(A_88,k1_xboole_0)
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_14,c_161])).

tff(c_283,plain,
    ( k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0)
    | ~ l1_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_280])).

tff(c_286,plain,
    ( k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_283])).

tff(c_287,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) = a_2_0_orders_2('#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_286])).

tff(c_30,plain,(
    ! [A_25] :
      ( l1_struct_0(A_25)
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_59,plain,(
    ! [A_42] :
      ( k1_struct_0(A_42) = k1_xboole_0
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,(
    ! [A_43] :
      ( k1_struct_0(A_43) = k1_xboole_0
      | ~ l1_orders_2(A_43) ) ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_68,plain,(
    k1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_64])).

tff(c_44,plain,(
    k1_orders_2('#skF_4',k1_struct_0('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_69,plain,(
    k1_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_44])).

tff(c_288,plain,(
    a_2_0_orders_2('#skF_4',k1_xboole_0) != u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_69])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k1_orders_2(A_23,B_24),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_292,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_28])).

tff(c_296,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_14,c_292])).

tff(c_297,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_4',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_296])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_316,plain,(
    r1_tarski(a_2_0_orders_2('#skF_4',k1_xboole_0),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_297,c_16])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_318,plain,
    ( a_2_0_orders_2('#skF_4',k1_xboole_0) = u1_struct_0('#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_316,c_4])).

tff(c_321,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_318])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_632,plain,(
    ! [A_118,A_119] :
      ( k1_orders_2(A_118,A_119) = a_2_0_orders_2(A_118,A_119)
      | ~ l1_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v4_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118)
      | ~ r1_tarski(A_119,u1_struct_0(A_118)) ) ),
    inference(resolution,[status(thm)],[c_18,c_161])).

tff(c_682,plain,(
    ! [A_118] :
      ( k1_orders_2(A_118,u1_struct_0(A_118)) = a_2_0_orders_2(A_118,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v4_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_8,c_632])).

tff(c_216,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1(k1_orders_2(A_78,B_79),k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_230,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k1_orders_2(A_78,B_79),u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_216,c_16])).

tff(c_351,plain,(
    ! [D_93,B_94,C_95] :
      ( r2_hidden('#skF_3'(D_93,B_94,C_95,D_93),C_95)
      | r2_hidden(D_93,a_2_0_orders_2(B_94,C_95))
      | ~ m1_subset_1(D_93,u1_struct_0(B_94))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(B_94)))
      | ~ l1_orders_2(B_94)
      | ~ v5_orders_2(B_94)
      | ~ v4_orders_2(B_94)
      | ~ v3_orders_2(B_94)
      | v2_struct_0(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_355,plain,(
    ! [D_93] :
      ( r2_hidden('#skF_3'(D_93,'#skF_4',a_2_0_orders_2('#skF_4',k1_xboole_0),D_93),a_2_0_orders_2('#skF_4',k1_xboole_0))
      | r2_hidden(D_93,a_2_0_orders_2('#skF_4',a_2_0_orders_2('#skF_4',k1_xboole_0)))
      | ~ m1_subset_1(D_93,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_297,c_351])).

tff(c_373,plain,(
    ! [D_93] :
      ( r2_hidden('#skF_3'(D_93,'#skF_4',a_2_0_orders_2('#skF_4',k1_xboole_0),D_93),a_2_0_orders_2('#skF_4',k1_xboole_0))
      | r2_hidden(D_93,a_2_0_orders_2('#skF_4',a_2_0_orders_2('#skF_4',k1_xboole_0)))
      | ~ m1_subset_1(D_93,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_355])).

tff(c_462,plain,(
    ! [D_101] :
      ( r2_hidden('#skF_3'(D_101,'#skF_4',a_2_0_orders_2('#skF_4',k1_xboole_0),D_101),a_2_0_orders_2('#skF_4',k1_xboole_0))
      | r2_hidden(D_101,a_2_0_orders_2('#skF_4',a_2_0_orders_2('#skF_4',k1_xboole_0)))
      | ~ m1_subset_1(D_101,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_373])).

tff(c_20,plain,(
    ! [A_13,C_15,B_14] :
      ( m1_subset_1(A_13,C_15)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(C_15))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_314,plain,(
    ! [A_13] :
      ( m1_subset_1(A_13,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_13,a_2_0_orders_2('#skF_4',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_297,c_20])).

tff(c_475,plain,(
    ! [D_101] :
      ( m1_subset_1('#skF_3'(D_101,'#skF_4',a_2_0_orders_2('#skF_4',k1_xboole_0),D_101),u1_struct_0('#skF_4'))
      | r2_hidden(D_101,a_2_0_orders_2('#skF_4',a_2_0_orders_2('#skF_4',k1_xboole_0)))
      | ~ m1_subset_1(D_101,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_462,c_314])).

tff(c_1181,plain,(
    ! [D_162,B_163,A_164] :
      ( r2_hidden('#skF_3'(D_162,B_163,A_164,D_162),A_164)
      | r2_hidden(D_162,a_2_0_orders_2(B_163,A_164))
      | ~ m1_subset_1(D_162,u1_struct_0(B_163))
      | ~ l1_orders_2(B_163)
      | ~ v5_orders_2(B_163)
      | ~ v4_orders_2(B_163)
      | ~ v3_orders_2(B_163)
      | v2_struct_0(B_163)
      | ~ r1_tarski(A_164,u1_struct_0(B_163)) ) ),
    inference(resolution,[status(thm)],[c_18,c_351])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_126,plain,(
    ! [A_65,B_66,C_67] :
      ( m1_subset_1('#skF_1'(A_65,B_66,C_67),B_66)
      | r1_tarski(B_66,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_141,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_tarski('#skF_1'(A_71,k1_zfmisc_1(B_72),C_73),B_72)
      | r1_tarski(k1_zfmisc_1(B_72),C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71))
      | ~ m1_subset_1(k1_zfmisc_1(B_72),k1_zfmisc_1(A_71)) ) ),
    inference(resolution,[status(thm)],[c_126,c_16])).

tff(c_75,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_83,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_14,c_75])).

tff(c_85,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(B_49,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_83,c_85])).

tff(c_150,plain,(
    ! [A_74,C_75] :
      ( '#skF_1'(A_74,k1_zfmisc_1(k1_xboole_0),C_75) = k1_xboole_0
      | r1_tarski(k1_zfmisc_1(k1_xboole_0),C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_74))
      | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(A_74)) ) ),
    inference(resolution,[status(thm)],[c_141,c_90])).

tff(c_160,plain,(
    ! [A_10] :
      ( '#skF_1'(A_10,k1_zfmisc_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0
      | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_177,plain,(
    r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_183,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_177,c_90])).

tff(c_22,plain,(
    ! [C_18,B_17,A_16] :
      ( ~ v1_xboole_0(C_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(C_18))
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_199,plain,(
    ! [B_17,A_16] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(B_17,k1_xboole_0)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_22])).

tff(c_213,plain,(
    ! [B_17,A_16] :
      ( ~ m1_subset_1(B_17,k1_xboole_0)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_199])).

tff(c_1507,plain,(
    ! [A_181,D_182,B_183] :
      ( ~ m1_subset_1(A_181,k1_xboole_0)
      | r2_hidden(D_182,a_2_0_orders_2(B_183,A_181))
      | ~ m1_subset_1(D_182,u1_struct_0(B_183))
      | ~ l1_orders_2(B_183)
      | ~ v5_orders_2(B_183)
      | ~ v4_orders_2(B_183)
      | ~ v3_orders_2(B_183)
      | v2_struct_0(B_183)
      | ~ r1_tarski(A_181,u1_struct_0(B_183)) ) ),
    inference(resolution,[status(thm)],[c_1181,c_213])).

tff(c_1577,plain,(
    ! [B_184,A_185,D_186] :
      ( ~ m1_subset_1(a_2_0_orders_2(B_184,A_185),k1_xboole_0)
      | ~ m1_subset_1(A_185,k1_xboole_0)
      | ~ m1_subset_1(D_186,u1_struct_0(B_184))
      | ~ l1_orders_2(B_184)
      | ~ v5_orders_2(B_184)
      | ~ v4_orders_2(B_184)
      | ~ v3_orders_2(B_184)
      | v2_struct_0(B_184)
      | ~ r1_tarski(A_185,u1_struct_0(B_184)) ) ),
    inference(resolution,[status(thm)],[c_1507,c_213])).

tff(c_1585,plain,(
    ! [A_185,D_101] :
      ( ~ m1_subset_1(a_2_0_orders_2('#skF_4',A_185),k1_xboole_0)
      | ~ m1_subset_1(A_185,k1_xboole_0)
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_185,u1_struct_0('#skF_4'))
      | r2_hidden(D_101,a_2_0_orders_2('#skF_4',a_2_0_orders_2('#skF_4',k1_xboole_0)))
      | ~ m1_subset_1(D_101,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_475,c_1577])).

tff(c_1597,plain,(
    ! [A_185,D_101] :
      ( ~ m1_subset_1(a_2_0_orders_2('#skF_4',A_185),k1_xboole_0)
      | ~ m1_subset_1(A_185,k1_xboole_0)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_185,u1_struct_0('#skF_4'))
      | r2_hidden(D_101,a_2_0_orders_2('#skF_4',a_2_0_orders_2('#skF_4',k1_xboole_0)))
      | ~ m1_subset_1(D_101,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1585])).

tff(c_1598,plain,(
    ! [A_185,D_101] :
      ( ~ m1_subset_1(a_2_0_orders_2('#skF_4',A_185),k1_xboole_0)
      | ~ m1_subset_1(A_185,k1_xboole_0)
      | ~ r1_tarski(A_185,u1_struct_0('#skF_4'))
      | r2_hidden(D_101,a_2_0_orders_2('#skF_4',a_2_0_orders_2('#skF_4',k1_xboole_0)))
      | ~ m1_subset_1(D_101,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1597])).

tff(c_1603,plain,(
    ! [A_187] :
      ( ~ m1_subset_1(a_2_0_orders_2('#skF_4',A_187),k1_xboole_0)
      | ~ m1_subset_1(A_187,k1_xboole_0)
      | ~ r1_tarski(A_187,u1_struct_0('#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_1598])).

tff(c_1618,plain,(
    ! [B_79] :
      ( ~ m1_subset_1(a_2_0_orders_2('#skF_4',k1_orders_2('#skF_4',B_79)),k1_xboole_0)
      | ~ m1_subset_1(k1_orders_2('#skF_4',B_79),k1_xboole_0)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_230,c_1603])).

tff(c_1651,plain,(
    ! [B_79] :
      ( ~ m1_subset_1(a_2_0_orders_2('#skF_4',k1_orders_2('#skF_4',B_79)),k1_xboole_0)
      | ~ m1_subset_1(k1_orders_2('#skF_4',B_79),k1_xboole_0)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1618])).

tff(c_1664,plain,(
    ! [B_188] :
      ( ~ m1_subset_1(a_2_0_orders_2('#skF_4',k1_orders_2('#skF_4',B_188)),k1_xboole_0)
      | ~ m1_subset_1(k1_orders_2('#skF_4',B_188),k1_xboole_0)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1651])).

tff(c_1679,plain,
    ( ~ m1_subset_1(a_2_0_orders_2('#skF_4',a_2_0_orders_2('#skF_4',u1_struct_0('#skF_4'))),k1_xboole_0)
    | ~ m1_subset_1(k1_orders_2('#skF_4',u1_struct_0('#skF_4')),k1_xboole_0)
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_1664])).

tff(c_1704,plain,
    ( ~ m1_subset_1(a_2_0_orders_2('#skF_4',a_2_0_orders_2('#skF_4',u1_struct_0('#skF_4'))),k1_xboole_0)
    | ~ m1_subset_1(k1_orders_2('#skF_4',u1_struct_0('#skF_4')),k1_xboole_0)
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1679])).

tff(c_1705,plain,
    ( ~ m1_subset_1(a_2_0_orders_2('#skF_4',a_2_0_orders_2('#skF_4',u1_struct_0('#skF_4'))),k1_xboole_0)
    | ~ m1_subset_1(k1_orders_2('#skF_4',u1_struct_0('#skF_4')),k1_xboole_0)
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1704])).

tff(c_1824,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1705])).

tff(c_1828,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_1824])).

tff(c_1832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1828])).

tff(c_1834,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1705])).

tff(c_12,plain,(
    ! [A_3,B_4,C_8] :
      ( m1_subset_1('#skF_1'(A_3,B_4,C_8),B_4)
      | r1_tarski(B_4,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ v1_xboole_0(C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,(
    ! [A_10,A_54] :
      ( ~ v1_xboole_0(A_10)
      | ~ r2_hidden(A_54,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_108])).

tff(c_115,plain,(
    ! [A_54] : ~ r2_hidden(A_54,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_366,plain,(
    ! [D_93,B_94] :
      ( r2_hidden('#skF_3'(D_93,B_94,k1_xboole_0,D_93),k1_xboole_0)
      | r2_hidden(D_93,a_2_0_orders_2(B_94,k1_xboole_0))
      | ~ m1_subset_1(D_93,u1_struct_0(B_94))
      | ~ l1_orders_2(B_94)
      | ~ v5_orders_2(B_94)
      | ~ v4_orders_2(B_94)
      | ~ v3_orders_2(B_94)
      | v2_struct_0(B_94) ) ),
    inference(resolution,[status(thm)],[c_14,c_351])).

tff(c_504,plain,(
    ! [D_107,B_108] :
      ( r2_hidden(D_107,a_2_0_orders_2(B_108,k1_xboole_0))
      | ~ m1_subset_1(D_107,u1_struct_0(B_108))
      | ~ l1_orders_2(B_108)
      | ~ v5_orders_2(B_108)
      | ~ v4_orders_2(B_108)
      | ~ v3_orders_2(B_108)
      | v2_struct_0(B_108) ) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_366])).

tff(c_10,plain,(
    ! [A_3,B_4,C_8] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_8),C_8)
      | r1_tarski(B_4,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3522,plain,(
    ! [B_248,B_249,A_250] :
      ( r1_tarski(B_248,a_2_0_orders_2(B_249,k1_xboole_0))
      | ~ m1_subset_1(a_2_0_orders_2(B_249,k1_xboole_0),k1_zfmisc_1(A_250))
      | ~ m1_subset_1(B_248,k1_zfmisc_1(A_250))
      | ~ m1_subset_1('#skF_1'(A_250,B_248,a_2_0_orders_2(B_249,k1_xboole_0)),u1_struct_0(B_249))
      | ~ l1_orders_2(B_249)
      | ~ v5_orders_2(B_249)
      | ~ v4_orders_2(B_249)
      | ~ v3_orders_2(B_249)
      | v2_struct_0(B_249) ) ),
    inference(resolution,[status(thm)],[c_504,c_10])).

tff(c_4595,plain,(
    ! [B_299,A_300] :
      ( ~ l1_orders_2(B_299)
      | ~ v5_orders_2(B_299)
      | ~ v4_orders_2(B_299)
      | ~ v3_orders_2(B_299)
      | v2_struct_0(B_299)
      | r1_tarski(u1_struct_0(B_299),a_2_0_orders_2(B_299,k1_xboole_0))
      | ~ m1_subset_1(a_2_0_orders_2(B_299,k1_xboole_0),k1_zfmisc_1(A_300))
      | ~ m1_subset_1(u1_struct_0(B_299),k1_zfmisc_1(A_300)) ) ),
    inference(resolution,[status(thm)],[c_12,c_3522])).

tff(c_4597,plain,
    ( ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_297,c_4595])).

tff(c_4605,plain,
    ( v2_struct_0('#skF_4')
    | r1_tarski(u1_struct_0('#skF_4'),a_2_0_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1834,c_52,c_50,c_48,c_46,c_4597])).

tff(c_4607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_54,c_4605])).

tff(c_4608,plain,(
    ! [A_10] : ~ v1_xboole_0(A_10) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_4610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4608,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.09/2.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.09/2.58  
% 7.09/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.58  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 7.21/2.58  
% 7.21/2.58  %Foreground sorts:
% 7.21/2.58  
% 7.21/2.58  
% 7.21/2.58  %Background operators:
% 7.21/2.58  
% 7.21/2.58  
% 7.21/2.58  %Foreground operators:
% 7.21/2.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.21/2.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.21/2.58  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.21/2.58  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 7.21/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.21/2.58  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 7.21/2.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.21/2.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.21/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.21/2.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.21/2.58  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.21/2.58  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.21/2.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.21/2.58  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.21/2.58  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.21/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.21/2.58  tff('#skF_4', type, '#skF_4': $i).
% 7.21/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.21/2.58  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 7.21/2.58  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 7.21/2.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.21/2.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.21/2.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.21/2.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.21/2.58  
% 7.21/2.62  tff(f_143, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k1_struct_0(A)) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_orders_2)).
% 7.21/2.62  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.21/2.62  tff(f_83, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 7.21/2.62  tff(f_102, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 7.21/2.62  tff(f_67, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 7.21/2.62  tff(f_98, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 7.21/2.62  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.21/2.62  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.21/2.62  tff(f_129, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 7.21/2.62  tff(f_56, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 7.21/2.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.21/2.62  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, B) => r2_hidden(D, C))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_subset_1)).
% 7.21/2.62  tff(f_63, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.21/2.62  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.21/2.62  tff(c_52, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.21/2.62  tff(c_50, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.21/2.62  tff(c_46, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.21/2.62  tff(c_48, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.21/2.62  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.21/2.62  tff(c_161, plain, (![A_76, B_77]: (k1_orders_2(A_76, B_77)=a_2_0_orders_2(A_76, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76) | ~v5_orders_2(A_76) | ~v4_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.21/2.62  tff(c_280, plain, (![A_88]: (k1_orders_2(A_88, k1_xboole_0)=a_2_0_orders_2(A_88, k1_xboole_0) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_14, c_161])).
% 7.21/2.62  tff(c_283, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0) | ~l1_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_280])).
% 7.21/2.62  tff(c_286, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_283])).
% 7.21/2.62  tff(c_287, plain, (k1_orders_2('#skF_4', k1_xboole_0)=a_2_0_orders_2('#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_286])).
% 7.21/2.62  tff(c_30, plain, (![A_25]: (l1_struct_0(A_25) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.21/2.62  tff(c_59, plain, (![A_42]: (k1_struct_0(A_42)=k1_xboole_0 | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.21/2.62  tff(c_64, plain, (![A_43]: (k1_struct_0(A_43)=k1_xboole_0 | ~l1_orders_2(A_43))), inference(resolution, [status(thm)], [c_30, c_59])).
% 7.21/2.62  tff(c_68, plain, (k1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_64])).
% 7.21/2.62  tff(c_44, plain, (k1_orders_2('#skF_4', k1_struct_0('#skF_4'))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.21/2.62  tff(c_69, plain, (k1_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_44])).
% 7.21/2.62  tff(c_288, plain, (a_2_0_orders_2('#skF_4', k1_xboole_0)!=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_69])).
% 7.21/2.62  tff(c_28, plain, (![A_23, B_24]: (m1_subset_1(k1_orders_2(A_23, B_24), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23) | ~v4_orders_2(A_23) | ~v3_orders_2(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.21/2.62  tff(c_292, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_287, c_28])).
% 7.21/2.62  tff(c_296, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_14, c_292])).
% 7.21/2.62  tff(c_297, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_296])).
% 7.21/2.62  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.21/2.62  tff(c_316, plain, (r1_tarski(a_2_0_orders_2('#skF_4', k1_xboole_0), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_297, c_16])).
% 7.21/2.62  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.21/2.62  tff(c_318, plain, (a_2_0_orders_2('#skF_4', k1_xboole_0)=u1_struct_0('#skF_4') | ~r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_316, c_4])).
% 7.21/2.62  tff(c_321, plain, (~r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_288, c_318])).
% 7.21/2.62  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.21/2.62  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.21/2.62  tff(c_632, plain, (![A_118, A_119]: (k1_orders_2(A_118, A_119)=a_2_0_orders_2(A_118, A_119) | ~l1_orders_2(A_118) | ~v5_orders_2(A_118) | ~v4_orders_2(A_118) | ~v3_orders_2(A_118) | v2_struct_0(A_118) | ~r1_tarski(A_119, u1_struct_0(A_118)))), inference(resolution, [status(thm)], [c_18, c_161])).
% 7.21/2.62  tff(c_682, plain, (![A_118]: (k1_orders_2(A_118, u1_struct_0(A_118))=a_2_0_orders_2(A_118, u1_struct_0(A_118)) | ~l1_orders_2(A_118) | ~v5_orders_2(A_118) | ~v4_orders_2(A_118) | ~v3_orders_2(A_118) | v2_struct_0(A_118))), inference(resolution, [status(thm)], [c_8, c_632])).
% 7.21/2.62  tff(c_216, plain, (![A_78, B_79]: (m1_subset_1(k1_orders_2(A_78, B_79), k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.21/2.62  tff(c_230, plain, (![A_78, B_79]: (r1_tarski(k1_orders_2(A_78, B_79), u1_struct_0(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(resolution, [status(thm)], [c_216, c_16])).
% 7.21/2.62  tff(c_351, plain, (![D_93, B_94, C_95]: (r2_hidden('#skF_3'(D_93, B_94, C_95, D_93), C_95) | r2_hidden(D_93, a_2_0_orders_2(B_94, C_95)) | ~m1_subset_1(D_93, u1_struct_0(B_94)) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(B_94))) | ~l1_orders_2(B_94) | ~v5_orders_2(B_94) | ~v4_orders_2(B_94) | ~v3_orders_2(B_94) | v2_struct_0(B_94))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.21/2.62  tff(c_355, plain, (![D_93]: (r2_hidden('#skF_3'(D_93, '#skF_4', a_2_0_orders_2('#skF_4', k1_xboole_0), D_93), a_2_0_orders_2('#skF_4', k1_xboole_0)) | r2_hidden(D_93, a_2_0_orders_2('#skF_4', a_2_0_orders_2('#skF_4', k1_xboole_0))) | ~m1_subset_1(D_93, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_297, c_351])).
% 7.21/2.62  tff(c_373, plain, (![D_93]: (r2_hidden('#skF_3'(D_93, '#skF_4', a_2_0_orders_2('#skF_4', k1_xboole_0), D_93), a_2_0_orders_2('#skF_4', k1_xboole_0)) | r2_hidden(D_93, a_2_0_orders_2('#skF_4', a_2_0_orders_2('#skF_4', k1_xboole_0))) | ~m1_subset_1(D_93, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_355])).
% 7.21/2.62  tff(c_462, plain, (![D_101]: (r2_hidden('#skF_3'(D_101, '#skF_4', a_2_0_orders_2('#skF_4', k1_xboole_0), D_101), a_2_0_orders_2('#skF_4', k1_xboole_0)) | r2_hidden(D_101, a_2_0_orders_2('#skF_4', a_2_0_orders_2('#skF_4', k1_xboole_0))) | ~m1_subset_1(D_101, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_373])).
% 7.21/2.62  tff(c_20, plain, (![A_13, C_15, B_14]: (m1_subset_1(A_13, C_15) | ~m1_subset_1(B_14, k1_zfmisc_1(C_15)) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.21/2.62  tff(c_314, plain, (![A_13]: (m1_subset_1(A_13, u1_struct_0('#skF_4')) | ~r2_hidden(A_13, a_2_0_orders_2('#skF_4', k1_xboole_0)))), inference(resolution, [status(thm)], [c_297, c_20])).
% 7.21/2.62  tff(c_475, plain, (![D_101]: (m1_subset_1('#skF_3'(D_101, '#skF_4', a_2_0_orders_2('#skF_4', k1_xboole_0), D_101), u1_struct_0('#skF_4')) | r2_hidden(D_101, a_2_0_orders_2('#skF_4', a_2_0_orders_2('#skF_4', k1_xboole_0))) | ~m1_subset_1(D_101, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_462, c_314])).
% 7.21/2.62  tff(c_1181, plain, (![D_162, B_163, A_164]: (r2_hidden('#skF_3'(D_162, B_163, A_164, D_162), A_164) | r2_hidden(D_162, a_2_0_orders_2(B_163, A_164)) | ~m1_subset_1(D_162, u1_struct_0(B_163)) | ~l1_orders_2(B_163) | ~v5_orders_2(B_163) | ~v4_orders_2(B_163) | ~v3_orders_2(B_163) | v2_struct_0(B_163) | ~r1_tarski(A_164, u1_struct_0(B_163)))), inference(resolution, [status(thm)], [c_18, c_351])).
% 7.21/2.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.21/2.62  tff(c_126, plain, (![A_65, B_66, C_67]: (m1_subset_1('#skF_1'(A_65, B_66, C_67), B_66) | r1_tarski(B_66, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.21/2.62  tff(c_141, plain, (![A_71, B_72, C_73]: (r1_tarski('#skF_1'(A_71, k1_zfmisc_1(B_72), C_73), B_72) | r1_tarski(k1_zfmisc_1(B_72), C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(A_71)) | ~m1_subset_1(k1_zfmisc_1(B_72), k1_zfmisc_1(A_71)))), inference(resolution, [status(thm)], [c_126, c_16])).
% 7.21/2.62  tff(c_75, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.21/2.62  tff(c_83, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_14, c_75])).
% 7.21/2.62  tff(c_85, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(B_49, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.21/2.62  tff(c_90, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_83, c_85])).
% 7.21/2.62  tff(c_150, plain, (![A_74, C_75]: ('#skF_1'(A_74, k1_zfmisc_1(k1_xboole_0), C_75)=k1_xboole_0 | r1_tarski(k1_zfmisc_1(k1_xboole_0), C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(A_74)) | ~m1_subset_1(k1_zfmisc_1(k1_xboole_0), k1_zfmisc_1(A_74)))), inference(resolution, [status(thm)], [c_141, c_90])).
% 7.21/2.62  tff(c_160, plain, (![A_10]: ('#skF_1'(A_10, k1_zfmisc_1(k1_xboole_0), k1_xboole_0)=k1_xboole_0 | r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_xboole_0) | ~m1_subset_1(k1_zfmisc_1(k1_xboole_0), k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_14, c_150])).
% 7.21/2.62  tff(c_177, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_160])).
% 7.21/2.62  tff(c_183, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_177, c_90])).
% 7.21/2.62  tff(c_22, plain, (![C_18, B_17, A_16]: (~v1_xboole_0(C_18) | ~m1_subset_1(B_17, k1_zfmisc_1(C_18)) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.21/2.62  tff(c_199, plain, (![B_17, A_16]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1(B_17, k1_xboole_0) | ~r2_hidden(A_16, B_17))), inference(superposition, [status(thm), theory('equality')], [c_183, c_22])).
% 7.21/2.62  tff(c_213, plain, (![B_17, A_16]: (~m1_subset_1(B_17, k1_xboole_0) | ~r2_hidden(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_199])).
% 7.21/2.62  tff(c_1507, plain, (![A_181, D_182, B_183]: (~m1_subset_1(A_181, k1_xboole_0) | r2_hidden(D_182, a_2_0_orders_2(B_183, A_181)) | ~m1_subset_1(D_182, u1_struct_0(B_183)) | ~l1_orders_2(B_183) | ~v5_orders_2(B_183) | ~v4_orders_2(B_183) | ~v3_orders_2(B_183) | v2_struct_0(B_183) | ~r1_tarski(A_181, u1_struct_0(B_183)))), inference(resolution, [status(thm)], [c_1181, c_213])).
% 7.21/2.62  tff(c_1577, plain, (![B_184, A_185, D_186]: (~m1_subset_1(a_2_0_orders_2(B_184, A_185), k1_xboole_0) | ~m1_subset_1(A_185, k1_xboole_0) | ~m1_subset_1(D_186, u1_struct_0(B_184)) | ~l1_orders_2(B_184) | ~v5_orders_2(B_184) | ~v4_orders_2(B_184) | ~v3_orders_2(B_184) | v2_struct_0(B_184) | ~r1_tarski(A_185, u1_struct_0(B_184)))), inference(resolution, [status(thm)], [c_1507, c_213])).
% 7.21/2.62  tff(c_1585, plain, (![A_185, D_101]: (~m1_subset_1(a_2_0_orders_2('#skF_4', A_185), k1_xboole_0) | ~m1_subset_1(A_185, k1_xboole_0) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_185, u1_struct_0('#skF_4')) | r2_hidden(D_101, a_2_0_orders_2('#skF_4', a_2_0_orders_2('#skF_4', k1_xboole_0))) | ~m1_subset_1(D_101, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_475, c_1577])).
% 7.21/2.62  tff(c_1597, plain, (![A_185, D_101]: (~m1_subset_1(a_2_0_orders_2('#skF_4', A_185), k1_xboole_0) | ~m1_subset_1(A_185, k1_xboole_0) | v2_struct_0('#skF_4') | ~r1_tarski(A_185, u1_struct_0('#skF_4')) | r2_hidden(D_101, a_2_0_orders_2('#skF_4', a_2_0_orders_2('#skF_4', k1_xboole_0))) | ~m1_subset_1(D_101, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_1585])).
% 7.21/2.62  tff(c_1598, plain, (![A_185, D_101]: (~m1_subset_1(a_2_0_orders_2('#skF_4', A_185), k1_xboole_0) | ~m1_subset_1(A_185, k1_xboole_0) | ~r1_tarski(A_185, u1_struct_0('#skF_4')) | r2_hidden(D_101, a_2_0_orders_2('#skF_4', a_2_0_orders_2('#skF_4', k1_xboole_0))) | ~m1_subset_1(D_101, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_1597])).
% 7.21/2.62  tff(c_1603, plain, (![A_187]: (~m1_subset_1(a_2_0_orders_2('#skF_4', A_187), k1_xboole_0) | ~m1_subset_1(A_187, k1_xboole_0) | ~r1_tarski(A_187, u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_1598])).
% 7.21/2.62  tff(c_1618, plain, (![B_79]: (~m1_subset_1(a_2_0_orders_2('#skF_4', k1_orders_2('#skF_4', B_79)), k1_xboole_0) | ~m1_subset_1(k1_orders_2('#skF_4', B_79), k1_xboole_0) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_230, c_1603])).
% 7.21/2.62  tff(c_1651, plain, (![B_79]: (~m1_subset_1(a_2_0_orders_2('#skF_4', k1_orders_2('#skF_4', B_79)), k1_xboole_0) | ~m1_subset_1(k1_orders_2('#skF_4', B_79), k1_xboole_0) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_1618])).
% 7.21/2.62  tff(c_1664, plain, (![B_188]: (~m1_subset_1(a_2_0_orders_2('#skF_4', k1_orders_2('#skF_4', B_188)), k1_xboole_0) | ~m1_subset_1(k1_orders_2('#skF_4', B_188), k1_xboole_0) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_1651])).
% 7.21/2.62  tff(c_1679, plain, (~m1_subset_1(a_2_0_orders_2('#skF_4', a_2_0_orders_2('#skF_4', u1_struct_0('#skF_4'))), k1_xboole_0) | ~m1_subset_1(k1_orders_2('#skF_4', u1_struct_0('#skF_4')), k1_xboole_0) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_682, c_1664])).
% 7.21/2.62  tff(c_1704, plain, (~m1_subset_1(a_2_0_orders_2('#skF_4', a_2_0_orders_2('#skF_4', u1_struct_0('#skF_4'))), k1_xboole_0) | ~m1_subset_1(k1_orders_2('#skF_4', u1_struct_0('#skF_4')), k1_xboole_0) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_1679])).
% 7.21/2.62  tff(c_1705, plain, (~m1_subset_1(a_2_0_orders_2('#skF_4', a_2_0_orders_2('#skF_4', u1_struct_0('#skF_4'))), k1_xboole_0) | ~m1_subset_1(k1_orders_2('#skF_4', u1_struct_0('#skF_4')), k1_xboole_0) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_1704])).
% 7.21/2.62  tff(c_1824, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_1705])).
% 7.21/2.62  tff(c_1828, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_1824])).
% 7.21/2.62  tff(c_1832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1828])).
% 7.21/2.62  tff(c_1834, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_1705])).
% 7.21/2.62  tff(c_12, plain, (![A_3, B_4, C_8]: (m1_subset_1('#skF_1'(A_3, B_4, C_8), B_4) | r1_tarski(B_4, C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.21/2.62  tff(c_108, plain, (![C_52, B_53, A_54]: (~v1_xboole_0(C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.21/2.62  tff(c_114, plain, (![A_10, A_54]: (~v1_xboole_0(A_10) | ~r2_hidden(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_108])).
% 7.21/2.62  tff(c_115, plain, (![A_54]: (~r2_hidden(A_54, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_114])).
% 7.21/2.62  tff(c_366, plain, (![D_93, B_94]: (r2_hidden('#skF_3'(D_93, B_94, k1_xboole_0, D_93), k1_xboole_0) | r2_hidden(D_93, a_2_0_orders_2(B_94, k1_xboole_0)) | ~m1_subset_1(D_93, u1_struct_0(B_94)) | ~l1_orders_2(B_94) | ~v5_orders_2(B_94) | ~v4_orders_2(B_94) | ~v3_orders_2(B_94) | v2_struct_0(B_94))), inference(resolution, [status(thm)], [c_14, c_351])).
% 7.21/2.62  tff(c_504, plain, (![D_107, B_108]: (r2_hidden(D_107, a_2_0_orders_2(B_108, k1_xboole_0)) | ~m1_subset_1(D_107, u1_struct_0(B_108)) | ~l1_orders_2(B_108) | ~v5_orders_2(B_108) | ~v4_orders_2(B_108) | ~v3_orders_2(B_108) | v2_struct_0(B_108))), inference(negUnitSimplification, [status(thm)], [c_115, c_366])).
% 7.21/2.62  tff(c_10, plain, (![A_3, B_4, C_8]: (~r2_hidden('#skF_1'(A_3, B_4, C_8), C_8) | r1_tarski(B_4, C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.21/2.62  tff(c_3522, plain, (![B_248, B_249, A_250]: (r1_tarski(B_248, a_2_0_orders_2(B_249, k1_xboole_0)) | ~m1_subset_1(a_2_0_orders_2(B_249, k1_xboole_0), k1_zfmisc_1(A_250)) | ~m1_subset_1(B_248, k1_zfmisc_1(A_250)) | ~m1_subset_1('#skF_1'(A_250, B_248, a_2_0_orders_2(B_249, k1_xboole_0)), u1_struct_0(B_249)) | ~l1_orders_2(B_249) | ~v5_orders_2(B_249) | ~v4_orders_2(B_249) | ~v3_orders_2(B_249) | v2_struct_0(B_249))), inference(resolution, [status(thm)], [c_504, c_10])).
% 7.21/2.62  tff(c_4595, plain, (![B_299, A_300]: (~l1_orders_2(B_299) | ~v5_orders_2(B_299) | ~v4_orders_2(B_299) | ~v3_orders_2(B_299) | v2_struct_0(B_299) | r1_tarski(u1_struct_0(B_299), a_2_0_orders_2(B_299, k1_xboole_0)) | ~m1_subset_1(a_2_0_orders_2(B_299, k1_xboole_0), k1_zfmisc_1(A_300)) | ~m1_subset_1(u1_struct_0(B_299), k1_zfmisc_1(A_300)))), inference(resolution, [status(thm)], [c_12, c_3522])).
% 7.21/2.62  tff(c_4597, plain, (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0)) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_297, c_4595])).
% 7.21/2.62  tff(c_4605, plain, (v2_struct_0('#skF_4') | r1_tarski(u1_struct_0('#skF_4'), a_2_0_orders_2('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1834, c_52, c_50, c_48, c_46, c_4597])).
% 7.21/2.62  tff(c_4607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_321, c_54, c_4605])).
% 7.21/2.62  tff(c_4608, plain, (![A_10]: (~v1_xboole_0(A_10))), inference(splitRight, [status(thm)], [c_114])).
% 7.21/2.62  tff(c_4610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4608, c_2])).
% 7.21/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.62  
% 7.21/2.62  Inference rules
% 7.21/2.62  ----------------------
% 7.21/2.62  #Ref     : 0
% 7.21/2.62  #Sup     : 921
% 7.21/2.62  #Fact    : 0
% 7.21/2.62  #Define  : 0
% 7.21/2.62  #Split   : 36
% 7.21/2.62  #Chain   : 0
% 7.21/2.62  #Close   : 0
% 7.21/2.62  
% 7.21/2.62  Ordering : KBO
% 7.21/2.62  
% 7.21/2.62  Simplification rules
% 7.21/2.62  ----------------------
% 7.21/2.62  #Subsume      : 215
% 7.21/2.62  #Demod        : 1904
% 7.21/2.62  #Tautology    : 145
% 7.21/2.62  #SimpNegUnit  : 323
% 7.21/2.62  #BackRed      : 5
% 7.21/2.62  
% 7.21/2.62  #Partial instantiations: 0
% 7.21/2.62  #Strategies tried      : 1
% 7.21/2.62  
% 7.21/2.62  Timing (in seconds)
% 7.21/2.62  ----------------------
% 7.21/2.63  Preprocessing        : 0.38
% 7.21/2.63  Parsing              : 0.19
% 7.21/2.63  CNF conversion       : 0.03
% 7.21/2.63  Main loop            : 1.40
% 7.21/2.63  Inferencing          : 0.40
% 7.21/2.63  Reduction            : 0.50
% 7.21/2.63  Demodulation         : 0.36
% 7.21/2.63  BG Simplification    : 0.05
% 7.21/2.63  Subsumption          : 0.35
% 7.21/2.63  Abstraction          : 0.07
% 7.21/2.63  MUC search           : 0.00
% 7.21/2.63  Cooper               : 0.00
% 7.21/2.63  Total                : 1.85
% 7.21/2.63  Index Insertion      : 0.00
% 7.21/2.63  Index Deletion       : 0.00
% 7.21/2.63  Index Matching       : 0.00
% 7.21/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
