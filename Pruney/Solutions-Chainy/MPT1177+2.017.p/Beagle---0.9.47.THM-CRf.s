%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:57 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 295 expanded)
%              Number of leaves         :   37 ( 124 expanded)
%              Depth                    :   12
%              Number of atoms          :  301 (1251 expanded)
%              Number of equality atoms :   21 (  47 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).

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

tff(c_186,plain,(
    ! [C_109,A_110,B_111] :
      ( m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m2_orders_2(C_109,A_110,B_111)
      | ~ m1_orders_1(B_111,k1_orders_1(u1_struct_0(A_110)))
      | ~ l1_orders_2(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v4_orders_2(A_110)
      | ~ v3_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_188,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_186])).

tff(c_191,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_188])).

tff(c_192,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_191])).

tff(c_74,plain,(
    ! [A_73,B_74] :
      ( r2_xboole_0(A_73,B_74)
      | B_74 = A_73
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_66,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_73,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54])).

tff(c_85,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_73])).

tff(c_91,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_117,plain,(
    ! [C_86,B_87,A_88] :
      ( r1_tarski(C_86,B_87)
      | ~ m1_orders_2(C_86,A_88,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_119,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_117])).

tff(c_122,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_119])).

tff(c_123,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_91,c_122])).

tff(c_128,plain,(
    ! [C_89,A_90,B_91] :
      ( m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ m2_orders_2(C_89,A_90,B_91)
      | ~ m1_orders_1(B_91,k1_orders_1(u1_struct_0(A_90)))
      | ~ l1_orders_2(A_90)
      | ~ v5_orders_2(A_90)
      | ~ v4_orders_2(A_90)
      | ~ v3_orders_2(A_90)
      | v2_struct_0(A_90) ) ),
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
    inference(negUnitSimplification,[status(thm)],[c_52,c_123,c_139])).

tff(c_142,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_145,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_66])).

tff(c_216,plain,(
    ! [C_119,A_120,B_121] :
      ( ~ m1_orders_2(C_119,A_120,B_121)
      | ~ m1_orders_2(B_121,A_120,C_119)
      | k1_xboole_0 = B_121
      | ~ m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_orders_2(A_120)
      | ~ v5_orders_2(A_120)
      | ~ v4_orders_2(A_120)
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_218,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_145,c_216])).

tff(c_221,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_192,c_145,c_218])).

tff(c_222,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_221])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_224,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_8])).

tff(c_14,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_204,plain,(
    ! [B_112,A_113,C_114] :
      ( r2_hidden(k1_funct_1(B_112,u1_struct_0(A_113)),C_114)
      | ~ m2_orders_2(C_114,A_113,B_112)
      | ~ m1_orders_1(B_112,k1_orders_1(u1_struct_0(A_113)))
      | ~ l1_orders_2(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_160,plain,(
    ! [C_94,B_95,A_96] :
      ( ~ v1_xboole_0(C_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(C_94))
      | ~ r2_hidden(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_163,plain,(
    ! [B_6,A_96,A_5] :
      ( ~ v1_xboole_0(B_6)
      | ~ r2_hidden(A_96,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_18,c_160])).

tff(c_209,plain,(
    ! [B_115,C_116,A_117,B_118] :
      ( ~ v1_xboole_0(B_115)
      | ~ r1_tarski(C_116,B_115)
      | ~ m2_orders_2(C_116,A_117,B_118)
      | ~ m1_orders_1(B_118,k1_orders_1(u1_struct_0(A_117)))
      | ~ l1_orders_2(A_117)
      | ~ v5_orders_2(A_117)
      | ~ v4_orders_2(A_117)
      | ~ v3_orders_2(A_117)
      | v2_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_204,c_163])).

tff(c_229,plain,(
    ! [B_122,A_123,B_124] :
      ( ~ v1_xboole_0(B_122)
      | ~ m2_orders_2(B_122,A_123,B_124)
      | ~ m1_orders_1(B_124,k1_orders_1(u1_struct_0(A_123)))
      | ~ l1_orders_2(A_123)
      | ~ v5_orders_2(A_123)
      | ~ v4_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_14,c_209])).

tff(c_231,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_229])).

tff(c_234,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_224,c_231])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_234])).

tff(c_237,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_242,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_237,c_6])).

tff(c_263,plain,(
    ! [B_129,A_130] :
      ( B_129 = A_130
      | ~ r1_tarski(B_129,A_130)
      | ~ r1_tarski(A_130,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_268,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_242,c_263])).

tff(c_273,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_40,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_294,plain,(
    ! [C_146,A_147,B_148] :
      ( m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ m2_orders_2(C_146,A_147,B_148)
      | ~ m1_orders_1(B_148,k1_orders_1(u1_struct_0(A_147)))
      | ~ l1_orders_2(A_147)
      | ~ v5_orders_2(A_147)
      | ~ v4_orders_2(A_147)
      | ~ v3_orders_2(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_296,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_294])).

tff(c_301,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_296])).

tff(c_302,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_301])).

tff(c_238,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_363,plain,(
    ! [C_166,A_167,D_168,B_169] :
      ( m1_orders_2(C_166,A_167,D_168)
      | m1_orders_2(D_168,A_167,C_166)
      | D_168 = C_166
      | ~ m2_orders_2(D_168,A_167,B_169)
      | ~ m2_orders_2(C_166,A_167,B_169)
      | ~ m1_orders_1(B_169,k1_orders_1(u1_struct_0(A_167)))
      | ~ l1_orders_2(A_167)
      | ~ v5_orders_2(A_167)
      | ~ v4_orders_2(A_167)
      | ~ v3_orders_2(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_365,plain,(
    ! [C_166] :
      ( m1_orders_2(C_166,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_166)
      | C_166 = '#skF_3'
      | ~ m2_orders_2(C_166,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_363])).

tff(c_370,plain,(
    ! [C_166] :
      ( m1_orders_2(C_166,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_166)
      | C_166 = '#skF_3'
      | ~ m2_orders_2(C_166,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_365])).

tff(c_376,plain,(
    ! [C_170] :
      ( m1_orders_2(C_170,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_170)
      | C_170 = '#skF_3'
      | ~ m2_orders_2(C_170,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_370])).

tff(c_382,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_376])).

tff(c_387,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_382])).

tff(c_388,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_395,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_273])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_395])).

tff(c_406,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_387])).

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

tff(c_415,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_406,c_28])).

tff(c_430,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_302,c_415])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_273,c_430])).

tff(c_433,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_441,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_237])).

tff(c_445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:10:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.37  
% 2.77/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.37  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.77/1.37  
% 2.77/1.37  %Foreground sorts:
% 2.77/1.37  
% 2.77/1.37  
% 2.77/1.37  %Background operators:
% 2.77/1.37  
% 2.77/1.37  
% 2.77/1.37  %Foreground operators:
% 2.77/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.77/1.37  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.77/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.37  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.77/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.37  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.77/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.37  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.77/1.37  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.77/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.37  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.77/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.77/1.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.77/1.37  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.77/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.37  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.77/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.37  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.77/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.77/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.37  
% 2.77/1.40  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.77/1.40  tff(f_204, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 2.77/1.40  tff(f_88, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.77/1.40  tff(f_107, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 2.77/1.40  tff(f_132, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 2.77/1.40  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.77/1.40  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.77/1.40  tff(f_151, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.77/1.40  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.77/1.40  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.77/1.40  tff(f_179, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 2.77/1.40  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.40  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.77/1.40  tff(c_50, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.77/1.40  tff(c_48, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.77/1.40  tff(c_46, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.77/1.40  tff(c_44, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.77/1.40  tff(c_42, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.77/1.40  tff(c_38, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.77/1.40  tff(c_186, plain, (![C_109, A_110, B_111]: (m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~m2_orders_2(C_109, A_110, B_111) | ~m1_orders_1(B_111, k1_orders_1(u1_struct_0(A_110))) | ~l1_orders_2(A_110) | ~v5_orders_2(A_110) | ~v4_orders_2(A_110) | ~v3_orders_2(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.77/1.40  tff(c_188, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_186])).
% 2.77/1.40  tff(c_191, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_188])).
% 2.77/1.40  tff(c_192, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_191])).
% 2.77/1.40  tff(c_74, plain, (![A_73, B_74]: (r2_xboole_0(A_73, B_74) | B_74=A_73 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.40  tff(c_60, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.77/1.40  tff(c_66, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 2.77/1.40  tff(c_54, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.77/1.40  tff(c_73, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54])).
% 2.77/1.40  tff(c_85, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_73])).
% 2.77/1.40  tff(c_91, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_85])).
% 2.77/1.40  tff(c_117, plain, (![C_86, B_87, A_88]: (r1_tarski(C_86, B_87) | ~m1_orders_2(C_86, A_88, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.77/1.40  tff(c_119, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_117])).
% 2.77/1.40  tff(c_122, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_119])).
% 2.77/1.40  tff(c_123, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_91, c_122])).
% 2.77/1.40  tff(c_128, plain, (![C_89, A_90, B_91]: (m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~m2_orders_2(C_89, A_90, B_91) | ~m1_orders_1(B_91, k1_orders_1(u1_struct_0(A_90))) | ~l1_orders_2(A_90) | ~v5_orders_2(A_90) | ~v4_orders_2(A_90) | ~v3_orders_2(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.77/1.40  tff(c_132, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_128])).
% 2.77/1.40  tff(c_139, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_132])).
% 2.77/1.40  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_123, c_139])).
% 2.77/1.40  tff(c_142, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_85])).
% 2.77/1.40  tff(c_145, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_66])).
% 2.77/1.40  tff(c_216, plain, (![C_119, A_120, B_121]: (~m1_orders_2(C_119, A_120, B_121) | ~m1_orders_2(B_121, A_120, C_119) | k1_xboole_0=B_121 | ~m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_orders_2(A_120) | ~v5_orders_2(A_120) | ~v4_orders_2(A_120) | ~v3_orders_2(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.77/1.40  tff(c_218, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_145, c_216])).
% 2.77/1.40  tff(c_221, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_192, c_145, c_218])).
% 2.77/1.40  tff(c_222, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_221])).
% 2.77/1.40  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.77/1.40  tff(c_224, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_8])).
% 2.77/1.40  tff(c_14, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.40  tff(c_204, plain, (![B_112, A_113, C_114]: (r2_hidden(k1_funct_1(B_112, u1_struct_0(A_113)), C_114) | ~m2_orders_2(C_114, A_113, B_112) | ~m1_orders_1(B_112, k1_orders_1(u1_struct_0(A_113))) | ~l1_orders_2(A_113) | ~v5_orders_2(A_113) | ~v4_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.77/1.40  tff(c_18, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.40  tff(c_160, plain, (![C_94, B_95, A_96]: (~v1_xboole_0(C_94) | ~m1_subset_1(B_95, k1_zfmisc_1(C_94)) | ~r2_hidden(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.77/1.40  tff(c_163, plain, (![B_6, A_96, A_5]: (~v1_xboole_0(B_6) | ~r2_hidden(A_96, A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_18, c_160])).
% 2.77/1.40  tff(c_209, plain, (![B_115, C_116, A_117, B_118]: (~v1_xboole_0(B_115) | ~r1_tarski(C_116, B_115) | ~m2_orders_2(C_116, A_117, B_118) | ~m1_orders_1(B_118, k1_orders_1(u1_struct_0(A_117))) | ~l1_orders_2(A_117) | ~v5_orders_2(A_117) | ~v4_orders_2(A_117) | ~v3_orders_2(A_117) | v2_struct_0(A_117))), inference(resolution, [status(thm)], [c_204, c_163])).
% 2.77/1.40  tff(c_229, plain, (![B_122, A_123, B_124]: (~v1_xboole_0(B_122) | ~m2_orders_2(B_122, A_123, B_124) | ~m1_orders_1(B_124, k1_orders_1(u1_struct_0(A_123))) | ~l1_orders_2(A_123) | ~v5_orders_2(A_123) | ~v4_orders_2(A_123) | ~v3_orders_2(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_14, c_209])).
% 2.77/1.40  tff(c_231, plain, (~v1_xboole_0('#skF_4') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_229])).
% 2.77/1.40  tff(c_234, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_224, c_231])).
% 2.77/1.40  tff(c_236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_234])).
% 2.77/1.40  tff(c_237, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 2.77/1.40  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.40  tff(c_242, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_237, c_6])).
% 2.77/1.40  tff(c_263, plain, (![B_129, A_130]: (B_129=A_130 | ~r1_tarski(B_129, A_130) | ~r1_tarski(A_130, B_129))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.40  tff(c_268, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_242, c_263])).
% 2.77/1.40  tff(c_273, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_268])).
% 2.77/1.40  tff(c_40, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 2.77/1.40  tff(c_294, plain, (![C_146, A_147, B_148]: (m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(A_147))) | ~m2_orders_2(C_146, A_147, B_148) | ~m1_orders_1(B_148, k1_orders_1(u1_struct_0(A_147))) | ~l1_orders_2(A_147) | ~v5_orders_2(A_147) | ~v4_orders_2(A_147) | ~v3_orders_2(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.77/1.40  tff(c_296, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_294])).
% 2.77/1.40  tff(c_301, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_296])).
% 2.77/1.40  tff(c_302, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_52, c_301])).
% 2.77/1.40  tff(c_238, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 2.77/1.40  tff(c_363, plain, (![C_166, A_167, D_168, B_169]: (m1_orders_2(C_166, A_167, D_168) | m1_orders_2(D_168, A_167, C_166) | D_168=C_166 | ~m2_orders_2(D_168, A_167, B_169) | ~m2_orders_2(C_166, A_167, B_169) | ~m1_orders_1(B_169, k1_orders_1(u1_struct_0(A_167))) | ~l1_orders_2(A_167) | ~v5_orders_2(A_167) | ~v4_orders_2(A_167) | ~v3_orders_2(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.77/1.40  tff(c_365, plain, (![C_166]: (m1_orders_2(C_166, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_166) | C_166='#skF_3' | ~m2_orders_2(C_166, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_363])).
% 2.77/1.40  tff(c_370, plain, (![C_166]: (m1_orders_2(C_166, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_166) | C_166='#skF_3' | ~m2_orders_2(C_166, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_365])).
% 2.77/1.40  tff(c_376, plain, (![C_170]: (m1_orders_2(C_170, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_170) | C_170='#skF_3' | ~m2_orders_2(C_170, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_370])).
% 2.77/1.40  tff(c_382, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_376])).
% 2.77/1.40  tff(c_387, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_238, c_382])).
% 2.77/1.40  tff(c_388, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_387])).
% 2.77/1.40  tff(c_395, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_388, c_273])).
% 2.77/1.40  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_395])).
% 2.77/1.40  tff(c_406, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_387])).
% 2.77/1.40  tff(c_28, plain, (![C_24, B_22, A_18]: (r1_tarski(C_24, B_22) | ~m1_orders_2(C_24, A_18, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_orders_2(A_18) | ~v5_orders_2(A_18) | ~v4_orders_2(A_18) | ~v3_orders_2(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.77/1.40  tff(c_415, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_406, c_28])).
% 2.77/1.40  tff(c_430, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_302, c_415])).
% 2.77/1.40  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_273, c_430])).
% 2.77/1.40  tff(c_433, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_268])).
% 2.77/1.40  tff(c_441, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_237])).
% 2.77/1.40  tff(c_445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_441])).
% 2.77/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.40  
% 2.77/1.40  Inference rules
% 2.77/1.40  ----------------------
% 2.77/1.40  #Ref     : 0
% 2.77/1.40  #Sup     : 63
% 2.77/1.40  #Fact    : 0
% 2.77/1.40  #Define  : 0
% 2.77/1.40  #Split   : 10
% 2.77/1.40  #Chain   : 0
% 2.77/1.40  #Close   : 0
% 2.77/1.40  
% 2.77/1.40  Ordering : KBO
% 2.77/1.40  
% 2.77/1.40  Simplification rules
% 2.77/1.40  ----------------------
% 2.77/1.40  #Subsume      : 11
% 2.77/1.40  #Demod        : 154
% 2.77/1.40  #Tautology    : 26
% 2.77/1.40  #SimpNegUnit  : 25
% 2.77/1.40  #BackRed      : 20
% 2.77/1.40  
% 2.77/1.40  #Partial instantiations: 0
% 2.77/1.40  #Strategies tried      : 1
% 2.77/1.40  
% 2.77/1.40  Timing (in seconds)
% 2.77/1.40  ----------------------
% 2.77/1.40  Preprocessing        : 0.33
% 2.77/1.40  Parsing              : 0.19
% 2.77/1.40  CNF conversion       : 0.03
% 2.77/1.40  Main loop            : 0.29
% 2.77/1.40  Inferencing          : 0.11
% 2.77/1.40  Reduction            : 0.10
% 2.77/1.40  Demodulation         : 0.07
% 2.77/1.40  BG Simplification    : 0.02
% 2.77/1.40  Subsumption          : 0.05
% 2.77/1.40  Abstraction          : 0.01
% 2.77/1.40  MUC search           : 0.00
% 2.77/1.40  Cooper               : 0.00
% 2.77/1.40  Total                : 0.67
% 2.77/1.40  Index Insertion      : 0.00
% 2.77/1.40  Index Deletion       : 0.00
% 2.77/1.40  Index Matching       : 0.00
% 2.77/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
