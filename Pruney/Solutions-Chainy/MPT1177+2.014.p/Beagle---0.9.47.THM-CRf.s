%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:57 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 304 expanded)
%              Number of leaves         :   42 ( 128 expanded)
%              Depth                    :   10
%              Number of atoms          :  305 (1251 expanded)
%              Number of equality atoms :   23 (  48 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_215,negated_conjecture,(
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

tff(f_162,axiom,(
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

tff(f_52,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_99,axiom,(
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

tff(f_118,axiom,(
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

tff(f_143,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_190,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_54,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_52,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_50,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_48,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_46,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_42,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_248,plain,(
    ! [B_119,A_120,C_121] :
      ( r2_hidden(k1_funct_1(B_119,u1_struct_0(A_120)),C_121)
      | ~ m2_orders_2(C_121,A_120,B_119)
      | ~ m1_orders_1(B_119,k1_orders_1(u1_struct_0(A_120)))
      | ~ l1_orders_2(A_120)
      | ~ v5_orders_2(A_120)
      | ~ v4_orders_2(A_120)
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_20,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_65,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_198,plain,(
    ! [C_101,B_102,A_103] :
      ( ~ v1_xboole_0(C_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(C_101))
      | ~ r2_hidden(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_201,plain,(
    ! [A_10,A_103] :
      ( ~ v1_xboole_0(A_10)
      | ~ r2_hidden(A_103,A_10) ) ),
    inference(resolution,[status(thm)],[c_65,c_198])).

tff(c_253,plain,(
    ! [C_122,A_123,B_124] :
      ( ~ v1_xboole_0(C_122)
      | ~ m2_orders_2(C_122,A_123,B_124)
      | ~ m1_orders_1(B_124,k1_orders_1(u1_struct_0(A_123)))
      | ~ l1_orders_2(A_123)
      | ~ v5_orders_2(A_123)
      | ~ v4_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_248,c_201])).

tff(c_255,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_253])).

tff(c_258,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_255])).

tff(c_259,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_258])).

tff(c_237,plain,(
    ! [C_116,A_117,B_118] :
      ( m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m2_orders_2(C_116,A_117,B_118)
      | ~ m1_orders_1(B_118,k1_orders_1(u1_struct_0(A_117)))
      | ~ l1_orders_2(A_117)
      | ~ v5_orders_2(A_117)
      | ~ v4_orders_2(A_117)
      | ~ v3_orders_2(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_239,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_237])).

tff(c_242,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_239])).

tff(c_243,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_242])).

tff(c_89,plain,(
    ! [A_79,B_80] :
      ( r2_xboole_0(A_79,B_80)
      | B_80 = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_82,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_100,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_89,c_82])).

tff(c_118,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_64,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_83,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_64])).

tff(c_160,plain,(
    ! [C_93,B_94,A_95] :
      ( r1_tarski(C_93,B_94)
      | ~ m1_orders_2(C_93,A_95,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_orders_2(A_95)
      | ~ v5_orders_2(A_95)
      | ~ v4_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_162,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_83,c_160])).

tff(c_165,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_162])).

tff(c_166,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_118,c_165])).

tff(c_167,plain,(
    ! [C_96,A_97,B_98] :
      ( m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m2_orders_2(C_96,A_97,B_98)
      | ~ m1_orders_1(B_98,k1_orders_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97)
      | ~ v5_orders_2(A_97)
      | ~ v4_orders_2(A_97)
      | ~ v3_orders_2(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_169,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_167])).

tff(c_174,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_169])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_166,c_174])).

tff(c_177,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_189,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_83])).

tff(c_260,plain,(
    ! [C_125,A_126,B_127] :
      ( ~ m1_orders_2(C_125,A_126,B_127)
      | ~ m1_orders_2(B_127,A_126,C_125)
      | k1_xboole_0 = B_127
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_262,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_189,c_260])).

tff(c_265,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_243,c_189,c_262])).

tff(c_266,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_265])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_84,plain,(
    ! [B_77,A_78] :
      ( ~ r1_xboole_0(B_77,A_78)
      | ~ r1_tarski(B_77,A_78)
      | v1_xboole_0(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_106,plain,(
    ! [A_81] :
      ( ~ r1_tarski(A_81,k1_xboole_0)
      | v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_16,c_84])).

tff(c_115,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_106])).

tff(c_269,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_115])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_269])).

tff(c_276,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_280,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_276,c_6])).

tff(c_296,plain,(
    ! [B_130,A_131] :
      ( B_130 = A_131
      | ~ r1_tarski(B_130,A_131)
      | ~ r1_tarski(A_131,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_303,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_296])).

tff(c_322,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_44,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_359,plain,(
    ! [C_147,A_148,B_149] :
      ( m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ m2_orders_2(C_147,A_148,B_149)
      | ~ m1_orders_1(B_149,k1_orders_1(u1_struct_0(A_148)))
      | ~ l1_orders_2(A_148)
      | ~ v5_orders_2(A_148)
      | ~ v4_orders_2(A_148)
      | ~ v3_orders_2(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_363,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_359])).

tff(c_370,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_363])).

tff(c_371,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_370])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_275,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_400,plain,(
    ! [C_162,A_163,D_164,B_165] :
      ( m1_orders_2(C_162,A_163,D_164)
      | m1_orders_2(D_164,A_163,C_162)
      | D_164 = C_162
      | ~ m2_orders_2(D_164,A_163,B_165)
      | ~ m2_orders_2(C_162,A_163,B_165)
      | ~ m1_orders_1(B_165,k1_orders_1(u1_struct_0(A_163)))
      | ~ l1_orders_2(A_163)
      | ~ v5_orders_2(A_163)
      | ~ v4_orders_2(A_163)
      | ~ v3_orders_2(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_402,plain,(
    ! [C_162] :
      ( m1_orders_2(C_162,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_162)
      | C_162 = '#skF_4'
      | ~ m2_orders_2(C_162,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_400])).

tff(c_407,plain,(
    ! [C_162] :
      ( m1_orders_2(C_162,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_162)
      | C_162 = '#skF_4'
      | ~ m2_orders_2(C_162,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_402])).

tff(c_413,plain,(
    ! [C_166] :
      ( m1_orders_2(C_166,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_166)
      | C_166 = '#skF_4'
      | ~ m2_orders_2(C_166,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_407])).

tff(c_419,plain,
    ( m1_orders_2('#skF_3','#skF_1','#skF_4')
    | m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_413])).

tff(c_424,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_419])).

tff(c_437,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_442,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_322])).

tff(c_451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_442])).

tff(c_452,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_32,plain,(
    ! [C_28,B_26,A_22] :
      ( r1_tarski(C_28,B_26)
      | ~ m1_orders_2(C_28,A_22,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_orders_2(A_22)
      | ~ v5_orders_2(A_22)
      | ~ v4_orders_2(A_22)
      | ~ v3_orders_2(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_459,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_452,c_32])).

tff(c_470,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_371,c_459])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_322,c_470])).

tff(c_473,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_477,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_276])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:01:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.47  
% 2.88/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.47  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.88/1.47  
% 2.88/1.47  %Foreground sorts:
% 2.88/1.47  
% 2.88/1.47  
% 2.88/1.47  %Background operators:
% 2.88/1.47  
% 2.88/1.47  
% 2.88/1.47  %Foreground operators:
% 2.88/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.88/1.47  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.88/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.47  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.88/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.47  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.88/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.88/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.47  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.88/1.47  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.88/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.47  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.88/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.88/1.47  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.88/1.47  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.88/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.47  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.88/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.47  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.88/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.88/1.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.88/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.88/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.47  
% 2.88/1.49  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.88/1.49  tff(f_215, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.88/1.49  tff(f_162, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.88/1.49  tff(f_52, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.88/1.49  tff(f_54, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.88/1.49  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.88/1.49  tff(f_99, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.88/1.49  tff(f_118, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.88/1.49  tff(f_143, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.88/1.49  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.88/1.49  tff(f_42, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.88/1.49  tff(f_50, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.88/1.49  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.88/1.49  tff(f_190, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.88/1.49  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.49  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 2.88/1.49  tff(c_54, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 2.88/1.49  tff(c_52, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 2.88/1.49  tff(c_50, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 2.88/1.49  tff(c_48, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 2.88/1.49  tff(c_46, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_215])).
% 2.88/1.49  tff(c_42, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 2.88/1.49  tff(c_248, plain, (![B_119, A_120, C_121]: (r2_hidden(k1_funct_1(B_119, u1_struct_0(A_120)), C_121) | ~m2_orders_2(C_121, A_120, B_119) | ~m1_orders_1(B_119, k1_orders_1(u1_struct_0(A_120))) | ~l1_orders_2(A_120) | ~v5_orders_2(A_120) | ~v4_orders_2(A_120) | ~v3_orders_2(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.88/1.49  tff(c_20, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.88/1.49  tff(c_22, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.88/1.49  tff(c_65, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.88/1.49  tff(c_198, plain, (![C_101, B_102, A_103]: (~v1_xboole_0(C_101) | ~m1_subset_1(B_102, k1_zfmisc_1(C_101)) | ~r2_hidden(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.88/1.49  tff(c_201, plain, (![A_10, A_103]: (~v1_xboole_0(A_10) | ~r2_hidden(A_103, A_10))), inference(resolution, [status(thm)], [c_65, c_198])).
% 2.88/1.49  tff(c_253, plain, (![C_122, A_123, B_124]: (~v1_xboole_0(C_122) | ~m2_orders_2(C_122, A_123, B_124) | ~m1_orders_1(B_124, k1_orders_1(u1_struct_0(A_123))) | ~l1_orders_2(A_123) | ~v5_orders_2(A_123) | ~v4_orders_2(A_123) | ~v3_orders_2(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_248, c_201])).
% 2.88/1.49  tff(c_255, plain, (~v1_xboole_0('#skF_4') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_253])).
% 2.88/1.49  tff(c_258, plain, (~v1_xboole_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_255])).
% 2.88/1.49  tff(c_259, plain, (~v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_258])).
% 2.88/1.49  tff(c_237, plain, (![C_116, A_117, B_118]: (m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~m2_orders_2(C_116, A_117, B_118) | ~m1_orders_1(B_118, k1_orders_1(u1_struct_0(A_117))) | ~l1_orders_2(A_117) | ~v5_orders_2(A_117) | ~v4_orders_2(A_117) | ~v3_orders_2(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.49  tff(c_239, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_237])).
% 2.88/1.49  tff(c_242, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_239])).
% 2.88/1.49  tff(c_243, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_242])).
% 2.88/1.49  tff(c_89, plain, (![A_79, B_80]: (r2_xboole_0(A_79, B_80) | B_80=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.49  tff(c_58, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 2.88/1.49  tff(c_82, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 2.88/1.49  tff(c_100, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_89, c_82])).
% 2.88/1.49  tff(c_118, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_100])).
% 2.88/1.49  tff(c_64, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 2.88/1.49  tff(c_83, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_64])).
% 2.88/1.49  tff(c_160, plain, (![C_93, B_94, A_95]: (r1_tarski(C_93, B_94) | ~m1_orders_2(C_93, A_95, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_orders_2(A_95) | ~v5_orders_2(A_95) | ~v4_orders_2(A_95) | ~v3_orders_2(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.88/1.49  tff(c_162, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_83, c_160])).
% 2.88/1.49  tff(c_165, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_162])).
% 2.88/1.49  tff(c_166, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_118, c_165])).
% 2.88/1.49  tff(c_167, plain, (![C_96, A_97, B_98]: (m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~m2_orders_2(C_96, A_97, B_98) | ~m1_orders_1(B_98, k1_orders_1(u1_struct_0(A_97))) | ~l1_orders_2(A_97) | ~v5_orders_2(A_97) | ~v4_orders_2(A_97) | ~v3_orders_2(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.49  tff(c_169, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_167])).
% 2.88/1.49  tff(c_174, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_169])).
% 2.88/1.49  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_166, c_174])).
% 2.88/1.49  tff(c_177, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_100])).
% 2.88/1.49  tff(c_189, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_83])).
% 2.88/1.49  tff(c_260, plain, (![C_125, A_126, B_127]: (~m1_orders_2(C_125, A_126, B_127) | ~m1_orders_2(B_127, A_126, C_125) | k1_xboole_0=B_127 | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.88/1.49  tff(c_262, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_189, c_260])).
% 2.88/1.49  tff(c_265, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_243, c_189, c_262])).
% 2.88/1.49  tff(c_266, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_265])).
% 2.88/1.49  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.49  tff(c_16, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.88/1.49  tff(c_84, plain, (![B_77, A_78]: (~r1_xboole_0(B_77, A_78) | ~r1_tarski(B_77, A_78) | v1_xboole_0(B_77))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.88/1.49  tff(c_106, plain, (![A_81]: (~r1_tarski(A_81, k1_xboole_0) | v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_16, c_84])).
% 2.88/1.49  tff(c_115, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_106])).
% 2.88/1.49  tff(c_269, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_115])).
% 2.88/1.49  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_269])).
% 2.88/1.49  tff(c_276, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 2.88/1.49  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.49  tff(c_280, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_276, c_6])).
% 2.88/1.49  tff(c_296, plain, (![B_130, A_131]: (B_130=A_131 | ~r1_tarski(B_130, A_131) | ~r1_tarski(A_131, B_130))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.49  tff(c_303, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_280, c_296])).
% 2.88/1.49  tff(c_322, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_303])).
% 2.88/1.49  tff(c_44, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 2.88/1.49  tff(c_359, plain, (![C_147, A_148, B_149]: (m1_subset_1(C_147, k1_zfmisc_1(u1_struct_0(A_148))) | ~m2_orders_2(C_147, A_148, B_149) | ~m1_orders_1(B_149, k1_orders_1(u1_struct_0(A_148))) | ~l1_orders_2(A_148) | ~v5_orders_2(A_148) | ~v4_orders_2(A_148) | ~v3_orders_2(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.88/1.49  tff(c_363, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_359])).
% 2.88/1.49  tff(c_370, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_363])).
% 2.88/1.49  tff(c_371, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_370])).
% 2.88/1.49  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.49  tff(c_275, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 2.88/1.49  tff(c_400, plain, (![C_162, A_163, D_164, B_165]: (m1_orders_2(C_162, A_163, D_164) | m1_orders_2(D_164, A_163, C_162) | D_164=C_162 | ~m2_orders_2(D_164, A_163, B_165) | ~m2_orders_2(C_162, A_163, B_165) | ~m1_orders_1(B_165, k1_orders_1(u1_struct_0(A_163))) | ~l1_orders_2(A_163) | ~v5_orders_2(A_163) | ~v4_orders_2(A_163) | ~v3_orders_2(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_190])).
% 2.88/1.49  tff(c_402, plain, (![C_162]: (m1_orders_2(C_162, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_162) | C_162='#skF_4' | ~m2_orders_2(C_162, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_400])).
% 2.88/1.49  tff(c_407, plain, (![C_162]: (m1_orders_2(C_162, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_162) | C_162='#skF_4' | ~m2_orders_2(C_162, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_402])).
% 2.88/1.49  tff(c_413, plain, (![C_166]: (m1_orders_2(C_166, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_166) | C_166='#skF_4' | ~m2_orders_2(C_166, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_407])).
% 2.88/1.49  tff(c_419, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_44, c_413])).
% 2.88/1.49  tff(c_424, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_275, c_419])).
% 2.88/1.49  tff(c_437, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_424])).
% 2.88/1.49  tff(c_442, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_437, c_322])).
% 2.88/1.49  tff(c_451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_442])).
% 2.88/1.49  tff(c_452, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_424])).
% 2.88/1.49  tff(c_32, plain, (![C_28, B_26, A_22]: (r1_tarski(C_28, B_26) | ~m1_orders_2(C_28, A_22, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_orders_2(A_22) | ~v5_orders_2(A_22) | ~v4_orders_2(A_22) | ~v3_orders_2(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.88/1.49  tff(c_459, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_452, c_32])).
% 2.88/1.49  tff(c_470, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_371, c_459])).
% 2.88/1.49  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_322, c_470])).
% 2.88/1.49  tff(c_473, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_303])).
% 2.88/1.49  tff(c_477, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_276])).
% 2.88/1.49  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_477])).
% 2.88/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.49  
% 2.88/1.49  Inference rules
% 2.88/1.49  ----------------------
% 2.88/1.49  #Ref     : 0
% 2.88/1.49  #Sup     : 63
% 2.88/1.49  #Fact    : 0
% 2.88/1.49  #Define  : 0
% 2.88/1.49  #Split   : 7
% 2.88/1.49  #Chain   : 0
% 2.88/1.49  #Close   : 0
% 2.88/1.49  
% 2.88/1.49  Ordering : KBO
% 2.88/1.49  
% 2.88/1.49  Simplification rules
% 2.88/1.49  ----------------------
% 2.88/1.49  #Subsume      : 5
% 2.88/1.49  #Demod        : 148
% 2.88/1.49  #Tautology    : 33
% 2.88/1.49  #SimpNegUnit  : 27
% 2.88/1.49  #BackRed      : 22
% 2.88/1.49  
% 2.88/1.49  #Partial instantiations: 0
% 2.88/1.49  #Strategies tried      : 1
% 2.88/1.49  
% 2.88/1.49  Timing (in seconds)
% 2.88/1.49  ----------------------
% 2.88/1.50  Preprocessing        : 0.35
% 2.88/1.50  Parsing              : 0.20
% 2.88/1.50  CNF conversion       : 0.03
% 2.88/1.50  Main loop            : 0.29
% 2.88/1.50  Inferencing          : 0.10
% 2.88/1.50  Reduction            : 0.09
% 2.88/1.50  Demodulation         : 0.07
% 2.88/1.50  BG Simplification    : 0.02
% 2.88/1.50  Subsumption          : 0.05
% 2.88/1.50  Abstraction          : 0.01
% 2.88/1.50  MUC search           : 0.00
% 2.88/1.50  Cooper               : 0.00
% 2.88/1.50  Total                : 0.68
% 2.88/1.50  Index Insertion      : 0.00
% 2.88/1.50  Index Deletion       : 0.00
% 2.88/1.50  Index Matching       : 0.00
% 2.88/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
