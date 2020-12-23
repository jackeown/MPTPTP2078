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
% DateTime   : Thu Dec  3 10:19:56 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 297 expanded)
%              Number of leaves         :   39 ( 125 expanded)
%              Depth                    :   10
%              Number of atoms          :  294 (1240 expanded)
%              Number of equality atoms :   23 (  48 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_204,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_orders_2(C,A,B)
               => ! [D] :
                    ( m2_orders_2(D,A,B)
                   => ( r2_xboole_0(C,D)
                    <=> m1_orders_2(C,A,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_orders_2(C,A,B)
             => r1_tarski(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_132,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( B != k1_xboole_0
                  & m1_orders_2(B,A,C)
                  & m1_orders_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_179,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ( C != D
                   => ( m1_orders_2(C,A,D)
                    <=> ~ m1_orders_2(D,A,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_50,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_48,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_46,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_44,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_42,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_38,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_190,plain,(
    ! [B_106,A_107,C_108] :
      ( r2_hidden(k1_funct_1(B_106,u1_struct_0(A_107)),C_108)
      | ~ m2_orders_2(C_108,A_107,B_106)
      | ~ m1_orders_1(B_106,k1_orders_1(u1_struct_0(A_107)))
      | ~ l1_orders_2(A_107)
      | ~ v5_orders_2(A_107)
      | ~ v4_orders_2(A_107)
      | ~ v3_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_16,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_153,plain,(
    ! [C_89,B_90,A_91] :
      ( ~ v1_xboole_0(C_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(C_89))
      | ~ r2_hidden(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_156,plain,(
    ! [A_6,A_91] :
      ( ~ v1_xboole_0(A_6)
      | ~ r2_hidden(A_91,A_6) ) ),
    inference(resolution,[status(thm)],[c_61,c_153])).

tff(c_195,plain,(
    ! [C_109,A_110,B_111] :
      ( ~ v1_xboole_0(C_109)
      | ~ m2_orders_2(C_109,A_110,B_111)
      | ~ m1_orders_1(B_111,k1_orders_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_190,c_156])).

tff(c_197,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_195])).

tff(c_200,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_197])).

tff(c_201,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_200])).

tff(c_172,plain,(
    ! [C_100,A_101,B_102] :
      ( m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m2_orders_2(C_100,A_101,B_102)
      | ~ m1_orders_1(B_102,k1_orders_1(u1_struct_0(A_101)))
      | ~ l1_orders_2(A_101)
      | ~ v5_orders_2(A_101)
      | ~ v4_orders_2(A_101)
      | ~ v3_orders_2(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_174,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_172])).

tff(c_177,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_174])).

tff(c_178,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_177])).

tff(c_85,plain,(
    ! [A_73,B_74] :
      ( r2_xboole_0(A_73,B_74)
      | B_74 = A_73
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_76,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_96,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_85,c_76])).

tff(c_102,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_60,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_77,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_60])).

tff(c_108,plain,(
    ! [C_80,B_81,A_82] :
      ( r1_tarski(C_80,B_81)
      | ~ m1_orders_2(C_80,A_82,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_110,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_77,c_108])).

tff(c_113,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_110])).

tff(c_114,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_102,c_113])).

tff(c_128,plain,(
    ! [C_86,A_87,B_88] :
      ( m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m2_orders_2(C_86,A_87,B_88)
      | ~ m1_orders_1(B_88,k1_orders_1(u1_struct_0(A_87)))
      | ~ l1_orders_2(A_87)
      | ~ v5_orders_2(A_87)
      | ~ v4_orders_2(A_87)
      | ~ v3_orders_2(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_132,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_128])).

tff(c_139,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_132])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_114,c_139])).

tff(c_142,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_144,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_77])).

tff(c_202,plain,(
    ! [C_112,A_113,B_114] :
      ( ~ m1_orders_2(C_112,A_113,B_114)
      | ~ m1_orders_2(B_114,A_113,C_112)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_204,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_144,c_202])).

tff(c_207,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_178,c_144,c_204])).

tff(c_208,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_207])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_210,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_8])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_210])).

tff(c_214,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_218,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_214,c_6])).

tff(c_220,plain,(
    ! [B_115,A_116] :
      ( B_115 = A_116
      | ~ r1_tarski(B_115,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_225,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_218,c_220])).

tff(c_230,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_40,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_264,plain,(
    ! [C_133,A_134,B_135] :
      ( m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m2_orders_2(C_133,A_134,B_135)
      | ~ m1_orders_1(B_135,k1_orders_1(u1_struct_0(A_134)))
      | ~ l1_orders_2(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_266,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_264])).

tff(c_271,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_266])).

tff(c_272,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_271])).

tff(c_14,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_213,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_304,plain,(
    ! [C_149,A_150,D_151,B_152] :
      ( m1_orders_2(C_149,A_150,D_151)
      | m1_orders_2(D_151,A_150,C_149)
      | D_151 = C_149
      | ~ m2_orders_2(D_151,A_150,B_152)
      | ~ m2_orders_2(C_149,A_150,B_152)
      | ~ m1_orders_1(B_152,k1_orders_1(u1_struct_0(A_150)))
      | ~ l1_orders_2(A_150)
      | ~ v5_orders_2(A_150)
      | ~ v4_orders_2(A_150)
      | ~ v3_orders_2(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_306,plain,(
    ! [C_149] :
      ( m1_orders_2(C_149,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_149)
      | C_149 = '#skF_3'
      | ~ m2_orders_2(C_149,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_304])).

tff(c_311,plain,(
    ! [C_149] :
      ( m1_orders_2(C_149,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_149)
      | C_149 = '#skF_3'
      | ~ m2_orders_2(C_149,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_306])).

tff(c_317,plain,(
    ! [C_153] :
      ( m1_orders_2(C_153,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_153)
      | C_153 = '#skF_3'
      | ~ m2_orders_2(C_153,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_311])).

tff(c_323,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_317])).

tff(c_328,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_323])).

tff(c_329,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_334,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_230])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_334])).

tff(c_344,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_28,plain,(
    ! [C_24,B_22,A_18] :
      ( r1_tarski(C_24,B_22)
      | ~ m1_orders_2(C_24,A_18,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_orders_2(A_18)
      | ~ v5_orders_2(A_18)
      | ~ v4_orders_2(A_18)
      | ~ v3_orders_2(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_365,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_344,c_28])).

tff(c_380,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_272,c_365])).

tff(c_382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_230,c_380])).

tff(c_383,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_387,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_214])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.38  
% 2.70/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.38  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.70/1.38  
% 2.70/1.38  %Foreground sorts:
% 2.70/1.38  
% 2.70/1.38  
% 2.70/1.38  %Background operators:
% 2.70/1.38  
% 2.70/1.38  
% 2.70/1.38  %Foreground operators:
% 2.70/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.70/1.38  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.70/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.38  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.70/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.38  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.70/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.38  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.70/1.38  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.70/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.38  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.70/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.70/1.38  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.70/1.38  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.70/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.38  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.70/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.38  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.70/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.70/1.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.70/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.38  
% 2.70/1.40  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.70/1.40  tff(f_204, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.70/1.40  tff(f_151, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.70/1.40  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.70/1.40  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.70/1.40  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.70/1.40  tff(f_88, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.70/1.40  tff(f_107, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.70/1.40  tff(f_132, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.70/1.40  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.70/1.40  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.70/1.40  tff(f_179, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.70/1.40  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.70/1.40  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.70/1.40  tff(c_50, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.70/1.40  tff(c_48, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.70/1.40  tff(c_46, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.70/1.40  tff(c_44, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.70/1.40  tff(c_42, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.70/1.40  tff(c_38, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.70/1.40  tff(c_190, plain, (![B_106, A_107, C_108]: (r2_hidden(k1_funct_1(B_106, u1_struct_0(A_107)), C_108) | ~m2_orders_2(C_108, A_107, B_106) | ~m1_orders_1(B_106, k1_orders_1(u1_struct_0(A_107))) | ~l1_orders_2(A_107) | ~v5_orders_2(A_107) | ~v4_orders_2(A_107) | ~v3_orders_2(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.70/1.40  tff(c_16, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.40  tff(c_18, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.40  tff(c_61, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.70/1.40  tff(c_153, plain, (![C_89, B_90, A_91]: (~v1_xboole_0(C_89) | ~m1_subset_1(B_90, k1_zfmisc_1(C_89)) | ~r2_hidden(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.70/1.40  tff(c_156, plain, (![A_6, A_91]: (~v1_xboole_0(A_6) | ~r2_hidden(A_91, A_6))), inference(resolution, [status(thm)], [c_61, c_153])).
% 2.70/1.40  tff(c_195, plain, (![C_109, A_110, B_111]: (~v1_xboole_0(C_109) | ~m2_orders_2(C_109, A_110, B_111) | ~m1_orders_1(B_111, k1_orders_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_190, c_156])).
% 2.70/1.40  tff(c_197, plain, (~v1_xboole_0('#skF_4') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_195])).
% 2.70/1.40  tff(c_200, plain, (~v1_xboole_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_197])).
% 2.70/1.40  tff(c_201, plain, (~v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_200])).
% 2.70/1.40  tff(c_172, plain, (![C_100, A_101, B_102]: (m1_subset_1(C_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~m2_orders_2(C_100, A_101, B_102) | ~m1_orders_1(B_102, k1_orders_1(u1_struct_0(A_101))) | ~l1_orders_2(A_101) | ~v5_orders_2(A_101) | ~v4_orders_2(A_101) | ~v3_orders_2(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.70/1.40  tff(c_174, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_172])).
% 2.70/1.40  tff(c_177, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_174])).
% 2.70/1.40  tff(c_178, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_177])).
% 2.70/1.40  tff(c_85, plain, (![A_73, B_74]: (r2_xboole_0(A_73, B_74) | B_74=A_73 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.70/1.40  tff(c_54, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.70/1.40  tff(c_76, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 2.70/1.40  tff(c_96, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_85, c_76])).
% 2.70/1.40  tff(c_102, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_96])).
% 2.70/1.40  tff(c_60, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.70/1.40  tff(c_77, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_60])).
% 2.70/1.40  tff(c_108, plain, (![C_80, B_81, A_82]: (r1_tarski(C_80, B_81) | ~m1_orders_2(C_80, A_82, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.70/1.40  tff(c_110, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_77, c_108])).
% 2.70/1.40  tff(c_113, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_110])).
% 2.70/1.40  tff(c_114, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_102, c_113])).
% 2.70/1.40  tff(c_128, plain, (![C_86, A_87, B_88]: (m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0(A_87))) | ~m2_orders_2(C_86, A_87, B_88) | ~m1_orders_1(B_88, k1_orders_1(u1_struct_0(A_87))) | ~l1_orders_2(A_87) | ~v5_orders_2(A_87) | ~v4_orders_2(A_87) | ~v3_orders_2(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.70/1.40  tff(c_132, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_128])).
% 2.70/1.40  tff(c_139, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_132])).
% 2.70/1.40  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_114, c_139])).
% 2.70/1.40  tff(c_142, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_96])).
% 2.70/1.40  tff(c_144, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_77])).
% 2.70/1.40  tff(c_202, plain, (![C_112, A_113, B_114]: (~m1_orders_2(C_112, A_113, B_114) | ~m1_orders_2(B_114, A_113, C_112) | k1_xboole_0=B_114 | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.70/1.40  tff(c_204, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_144, c_202])).
% 2.70/1.40  tff(c_207, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_178, c_144, c_204])).
% 2.70/1.40  tff(c_208, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_207])).
% 2.70/1.40  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.40  tff(c_210, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_8])).
% 2.70/1.40  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_210])).
% 2.70/1.40  tff(c_214, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 2.70/1.40  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.70/1.40  tff(c_218, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_214, c_6])).
% 2.70/1.40  tff(c_220, plain, (![B_115, A_116]: (B_115=A_116 | ~r1_tarski(B_115, A_116) | ~r1_tarski(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.40  tff(c_225, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_218, c_220])).
% 2.70/1.40  tff(c_230, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_225])).
% 2.70/1.40  tff(c_40, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.70/1.40  tff(c_264, plain, (![C_133, A_134, B_135]: (m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~m2_orders_2(C_133, A_134, B_135) | ~m1_orders_1(B_135, k1_orders_1(u1_struct_0(A_134))) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.70/1.40  tff(c_266, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_264])).
% 2.70/1.40  tff(c_271, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_266])).
% 2.70/1.40  tff(c_272, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_271])).
% 2.70/1.40  tff(c_14, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.40  tff(c_213, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 2.70/1.40  tff(c_304, plain, (![C_149, A_150, D_151, B_152]: (m1_orders_2(C_149, A_150, D_151) | m1_orders_2(D_151, A_150, C_149) | D_151=C_149 | ~m2_orders_2(D_151, A_150, B_152) | ~m2_orders_2(C_149, A_150, B_152) | ~m1_orders_1(B_152, k1_orders_1(u1_struct_0(A_150))) | ~l1_orders_2(A_150) | ~v5_orders_2(A_150) | ~v4_orders_2(A_150) | ~v3_orders_2(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.70/1.40  tff(c_306, plain, (![C_149]: (m1_orders_2(C_149, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_149) | C_149='#skF_3' | ~m2_orders_2(C_149, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_304])).
% 2.70/1.40  tff(c_311, plain, (![C_149]: (m1_orders_2(C_149, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_149) | C_149='#skF_3' | ~m2_orders_2(C_149, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_306])).
% 2.70/1.40  tff(c_317, plain, (![C_153]: (m1_orders_2(C_153, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_153) | C_153='#skF_3' | ~m2_orders_2(C_153, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_311])).
% 2.70/1.40  tff(c_323, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_317])).
% 2.70/1.40  tff(c_328, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_213, c_323])).
% 2.70/1.40  tff(c_329, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_328])).
% 2.70/1.40  tff(c_334, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_230])).
% 2.70/1.40  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_334])).
% 2.70/1.40  tff(c_344, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_328])).
% 2.70/1.40  tff(c_28, plain, (![C_24, B_22, A_18]: (r1_tarski(C_24, B_22) | ~m1_orders_2(C_24, A_18, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_orders_2(A_18) | ~v5_orders_2(A_18) | ~v4_orders_2(A_18) | ~v3_orders_2(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.70/1.40  tff(c_365, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_344, c_28])).
% 2.70/1.40  tff(c_380, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_272, c_365])).
% 2.70/1.40  tff(c_382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_230, c_380])).
% 2.70/1.40  tff(c_383, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_225])).
% 2.70/1.40  tff(c_387, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_383, c_214])).
% 2.70/1.40  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_387])).
% 2.70/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.40  
% 2.70/1.40  Inference rules
% 2.70/1.40  ----------------------
% 2.70/1.40  #Ref     : 0
% 2.70/1.40  #Sup     : 48
% 2.70/1.40  #Fact    : 0
% 2.70/1.40  #Define  : 0
% 2.70/1.40  #Split   : 6
% 2.70/1.40  #Chain   : 0
% 2.70/1.40  #Close   : 0
% 2.70/1.40  
% 2.70/1.40  Ordering : KBO
% 2.70/1.40  
% 2.70/1.40  Simplification rules
% 2.70/1.40  ----------------------
% 2.70/1.40  #Subsume      : 5
% 2.70/1.40  #Demod        : 151
% 2.70/1.40  #Tautology    : 24
% 2.70/1.40  #SimpNegUnit  : 28
% 2.70/1.40  #BackRed      : 18
% 2.70/1.40  
% 2.70/1.40  #Partial instantiations: 0
% 2.70/1.40  #Strategies tried      : 1
% 2.70/1.40  
% 2.70/1.40  Timing (in seconds)
% 2.70/1.40  ----------------------
% 2.70/1.41  Preprocessing        : 0.34
% 2.70/1.41  Parsing              : 0.19
% 2.70/1.41  CNF conversion       : 0.03
% 2.70/1.41  Main loop            : 0.28
% 2.70/1.41  Inferencing          : 0.10
% 2.70/1.41  Reduction            : 0.09
% 2.70/1.41  Demodulation         : 0.07
% 2.70/1.41  BG Simplification    : 0.02
% 2.70/1.41  Subsumption          : 0.05
% 2.70/1.41  Abstraction          : 0.01
% 2.70/1.41  MUC search           : 0.00
% 2.70/1.41  Cooper               : 0.00
% 2.70/1.41  Total                : 0.67
% 2.70/1.41  Index Insertion      : 0.00
% 2.70/1.41  Index Deletion       : 0.00
% 2.70/1.41  Index Matching       : 0.00
% 2.70/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
