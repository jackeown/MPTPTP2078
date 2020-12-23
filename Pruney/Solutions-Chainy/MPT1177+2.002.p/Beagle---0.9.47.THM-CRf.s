%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:55 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 452 expanded)
%              Number of leaves         :   38 ( 184 expanded)
%              Depth                    :   15
%              Number of atoms          :  308 (2020 expanded)
%              Number of equality atoms :   23 (  74 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

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

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_188,negated_conjecture,(
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

tff(f_91,axiom,(
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

tff(f_110,axiom,(
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

tff(f_135,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v6_orders_2(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ( m2_orders_2(C,A,B)
              <=> ( C != k1_xboole_0
                  & r2_wellord1(u1_orders_2(A),C)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,C)
                       => k1_funct_1(B,k1_orders_2(A,k3_orders_2(A,C,D))) = D ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_163,axiom,(
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
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_40,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_42,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_50,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_48,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_46,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_44,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_137,plain,(
    ! [C_88,A_89,B_90] :
      ( v6_orders_2(C_88,A_89)
      | ~ m2_orders_2(C_88,A_89,B_90)
      | ~ m1_orders_1(B_90,k1_orders_1(u1_struct_0(A_89)))
      | ~ l1_orders_2(A_89)
      | ~ v5_orders_2(A_89)
      | ~ v4_orders_2(A_89)
      | ~ v3_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_139,plain,
    ( v6_orders_2('#skF_4','#skF_2')
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_137])).

tff(c_142,plain,
    ( v6_orders_2('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_139])).

tff(c_143,plain,(
    v6_orders_2('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_142])).

tff(c_152,plain,(
    ! [C_94,A_95,B_96] :
      ( m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m2_orders_2(C_94,A_95,B_96)
      | ~ m1_orders_1(B_96,k1_orders_1(u1_struct_0(A_95)))
      | ~ l1_orders_2(A_95)
      | ~ v5_orders_2(A_95)
      | ~ v4_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_154,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_152])).

tff(c_157,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_154])).

tff(c_158,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_157])).

tff(c_68,plain,(
    ! [A_75,B_76] :
      ( r2_xboole_0(A_75,B_76)
      | B_76 = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_65,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_67,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54])).

tff(c_79,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_67])).

tff(c_92,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_106,plain,(
    ! [C_82,B_83,A_84] :
      ( r1_tarski(C_82,B_83)
      | ~ m1_orders_2(C_82,A_84,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_orders_2(A_84)
      | ~ v5_orders_2(A_84)
      | ~ v4_orders_2(A_84)
      | ~ v3_orders_2(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_108,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_65,c_106])).

tff(c_111,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_108])).

tff(c_112,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_92,c_111])).

tff(c_38,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_113,plain,(
    ! [C_85,A_86,B_87] :
      ( m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m2_orders_2(C_85,A_86,B_87)
      | ~ m1_orders_1(B_87,k1_orders_1(u1_struct_0(A_86)))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86)
      | ~ v3_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_117,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_113])).

tff(c_124,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_117])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_112,c_124])).

tff(c_127,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_130,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_65])).

tff(c_160,plain,(
    ! [C_99,A_100,B_101] :
      ( ~ m1_orders_2(C_99,A_100,B_101)
      | ~ m1_orders_2(B_101,A_100,C_99)
      | k1_xboole_0 = B_101
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_orders_2(A_100)
      | ~ v5_orders_2(A_100)
      | ~ v4_orders_2(A_100)
      | ~ v3_orders_2(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_162,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_160])).

tff(c_165,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_158,c_130,c_162])).

tff(c_166,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_165])).

tff(c_24,plain,(
    ! [A_5,B_17] :
      ( ~ m2_orders_2(k1_xboole_0,A_5,B_17)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ v6_orders_2(k1_xboole_0,A_5)
      | ~ m1_orders_1(B_17,k1_orders_1(u1_struct_0(A_5)))
      | ~ l1_orders_2(A_5)
      | ~ v5_orders_2(A_5)
      | ~ v4_orders_2(A_5)
      | ~ v3_orders_2(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_180,plain,(
    ! [A_105,B_106] :
      ( ~ m2_orders_2('#skF_4',A_105,B_106)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ v6_orders_2('#skF_4',A_105)
      | ~ m1_orders_1(B_106,k1_orders_1(u1_struct_0(A_105)))
      | ~ l1_orders_2(A_105)
      | ~ v5_orders_2(A_105)
      | ~ v4_orders_2(A_105)
      | ~ v3_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_166,c_166,c_24])).

tff(c_182,plain,(
    ! [B_106] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_106)
      | ~ v6_orders_2('#skF_4','#skF_2')
      | ~ m1_orders_1(B_106,k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_158,c_180])).

tff(c_185,plain,(
    ! [B_106] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_106)
      | ~ m1_orders_1(B_106,k1_orders_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_143,c_182])).

tff(c_187,plain,(
    ! [B_107] :
      ( ~ m2_orders_2('#skF_4','#skF_2',B_107)
      | ~ m1_orders_1(B_107,k1_orders_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_185])).

tff(c_190,plain,(
    ~ m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_187])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_190])).

tff(c_195,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_209,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_195,c_6])).

tff(c_224,plain,(
    ! [B_110,A_111] :
      ( B_110 = A_111
      | ~ r1_tarski(B_110,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_229,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_209,c_224])).

tff(c_234,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_249,plain,(
    ! [C_118,A_119,B_120] :
      ( m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m2_orders_2(C_118,A_119,B_120)
      | ~ m1_orders_1(B_120,k1_orders_1(u1_struct_0(A_119)))
      | ~ l1_orders_2(A_119)
      | ~ v5_orders_2(A_119)
      | ~ v4_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_251,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_249])).

tff(c_256,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_251])).

tff(c_257,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_256])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_196,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_278,plain,(
    ! [C_133,A_134,D_135,B_136] :
      ( m1_orders_2(C_133,A_134,D_135)
      | m1_orders_2(D_135,A_134,C_133)
      | D_135 = C_133
      | ~ m2_orders_2(D_135,A_134,B_136)
      | ~ m2_orders_2(C_133,A_134,B_136)
      | ~ m1_orders_1(B_136,k1_orders_1(u1_struct_0(A_134)))
      | ~ l1_orders_2(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_280,plain,(
    ! [C_133] :
      ( m1_orders_2(C_133,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_133)
      | C_133 = '#skF_4'
      | ~ m2_orders_2(C_133,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_278])).

tff(c_285,plain,(
    ! [C_133] :
      ( m1_orders_2(C_133,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_133)
      | C_133 = '#skF_4'
      | ~ m2_orders_2(C_133,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_280])).

tff(c_304,plain,(
    ! [C_140] :
      ( m1_orders_2(C_140,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_140)
      | C_140 = '#skF_4'
      | ~ m2_orders_2(C_140,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_285])).

tff(c_310,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_304])).

tff(c_315,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_310])).

tff(c_316,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_320,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_234])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_320])).

tff(c_331,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_30,plain,(
    ! [C_37,B_35,A_31] :
      ( r1_tarski(C_37,B_35)
      | ~ m1_orders_2(C_37,A_31,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_orders_2(A_31)
      | ~ v5_orders_2(A_31)
      | ~ v4_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_350,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_331,c_30])).

tff(c_361,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_257,c_350])).

tff(c_363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_234,c_361])).

tff(c_364,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_368,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_195])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.33  
% 2.36/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.33  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.64/1.33  
% 2.64/1.33  %Foreground sorts:
% 2.64/1.33  
% 2.64/1.33  
% 2.64/1.33  %Background operators:
% 2.64/1.33  
% 2.64/1.33  
% 2.64/1.33  %Foreground operators:
% 2.64/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.64/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.64/1.33  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.64/1.33  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.64/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.33  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.64/1.33  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.64/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.33  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.64/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.64/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.33  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.64/1.33  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.64/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.33  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.64/1.33  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.64/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.64/1.33  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.64/1.33  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.64/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.33  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.64/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.33  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.64/1.33  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.64/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.64/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.33  
% 2.64/1.35  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.64/1.35  tff(f_188, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.64/1.35  tff(f_91, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.64/1.35  tff(f_110, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.64/1.35  tff(f_135, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.64/1.35  tff(f_71, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 2.64/1.35  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.64/1.35  tff(f_163, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.64/1.35  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.35  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.64/1.35  tff(c_40, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.64/1.35  tff(c_42, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.64/1.35  tff(c_50, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.64/1.35  tff(c_48, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.64/1.35  tff(c_46, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.64/1.35  tff(c_44, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.64/1.35  tff(c_137, plain, (![C_88, A_89, B_90]: (v6_orders_2(C_88, A_89) | ~m2_orders_2(C_88, A_89, B_90) | ~m1_orders_1(B_90, k1_orders_1(u1_struct_0(A_89))) | ~l1_orders_2(A_89) | ~v5_orders_2(A_89) | ~v4_orders_2(A_89) | ~v3_orders_2(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.64/1.35  tff(c_139, plain, (v6_orders_2('#skF_4', '#skF_2') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_137])).
% 2.64/1.35  tff(c_142, plain, (v6_orders_2('#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_139])).
% 2.64/1.35  tff(c_143, plain, (v6_orders_2('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_142])).
% 2.64/1.35  tff(c_152, plain, (![C_94, A_95, B_96]: (m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~m2_orders_2(C_94, A_95, B_96) | ~m1_orders_1(B_96, k1_orders_1(u1_struct_0(A_95))) | ~l1_orders_2(A_95) | ~v5_orders_2(A_95) | ~v4_orders_2(A_95) | ~v3_orders_2(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.64/1.35  tff(c_154, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_152])).
% 2.64/1.35  tff(c_157, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_154])).
% 2.64/1.35  tff(c_158, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_157])).
% 2.64/1.35  tff(c_68, plain, (![A_75, B_76]: (r2_xboole_0(A_75, B_76) | B_76=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.35  tff(c_60, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.64/1.35  tff(c_65, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 2.64/1.35  tff(c_54, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.64/1.35  tff(c_67, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_54])).
% 2.64/1.35  tff(c_79, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_67])).
% 2.64/1.35  tff(c_92, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_79])).
% 2.64/1.35  tff(c_106, plain, (![C_82, B_83, A_84]: (r1_tarski(C_82, B_83) | ~m1_orders_2(C_82, A_84, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_orders_2(A_84) | ~v5_orders_2(A_84) | ~v4_orders_2(A_84) | ~v3_orders_2(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.64/1.35  tff(c_108, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_65, c_106])).
% 2.64/1.35  tff(c_111, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_108])).
% 2.64/1.35  tff(c_112, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_92, c_111])).
% 2.64/1.35  tff(c_38, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.64/1.35  tff(c_113, plain, (![C_85, A_86, B_87]: (m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~m2_orders_2(C_85, A_86, B_87) | ~m1_orders_1(B_87, k1_orders_1(u1_struct_0(A_86))) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86) | ~v3_orders_2(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.64/1.35  tff(c_117, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_113])).
% 2.64/1.35  tff(c_124, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_117])).
% 2.64/1.35  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_112, c_124])).
% 2.64/1.35  tff(c_127, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_79])).
% 2.64/1.35  tff(c_130, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_65])).
% 2.64/1.35  tff(c_160, plain, (![C_99, A_100, B_101]: (~m1_orders_2(C_99, A_100, B_101) | ~m1_orders_2(B_101, A_100, C_99) | k1_xboole_0=B_101 | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_orders_2(A_100) | ~v5_orders_2(A_100) | ~v4_orders_2(A_100) | ~v3_orders_2(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.64/1.35  tff(c_162, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_130, c_160])).
% 2.64/1.35  tff(c_165, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_158, c_130, c_162])).
% 2.64/1.35  tff(c_166, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_165])).
% 2.64/1.35  tff(c_24, plain, (![A_5, B_17]: (~m2_orders_2(k1_xboole_0, A_5, B_17) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_5))) | ~v6_orders_2(k1_xboole_0, A_5) | ~m1_orders_1(B_17, k1_orders_1(u1_struct_0(A_5))) | ~l1_orders_2(A_5) | ~v5_orders_2(A_5) | ~v4_orders_2(A_5) | ~v3_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.64/1.35  tff(c_180, plain, (![A_105, B_106]: (~m2_orders_2('#skF_4', A_105, B_106) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_105))) | ~v6_orders_2('#skF_4', A_105) | ~m1_orders_1(B_106, k1_orders_1(u1_struct_0(A_105))) | ~l1_orders_2(A_105) | ~v5_orders_2(A_105) | ~v4_orders_2(A_105) | ~v3_orders_2(A_105) | v2_struct_0(A_105))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_166, c_166, c_24])).
% 2.64/1.35  tff(c_182, plain, (![B_106]: (~m2_orders_2('#skF_4', '#skF_2', B_106) | ~v6_orders_2('#skF_4', '#skF_2') | ~m1_orders_1(B_106, k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_158, c_180])).
% 2.64/1.35  tff(c_185, plain, (![B_106]: (~m2_orders_2('#skF_4', '#skF_2', B_106) | ~m1_orders_1(B_106, k1_orders_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_143, c_182])).
% 2.64/1.35  tff(c_187, plain, (![B_107]: (~m2_orders_2('#skF_4', '#skF_2', B_107) | ~m1_orders_1(B_107, k1_orders_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_185])).
% 2.64/1.35  tff(c_190, plain, (~m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_187])).
% 2.64/1.35  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_190])).
% 2.64/1.35  tff(c_195, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 2.64/1.35  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.35  tff(c_209, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_195, c_6])).
% 2.64/1.35  tff(c_224, plain, (![B_110, A_111]: (B_110=A_111 | ~r1_tarski(B_110, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.64/1.35  tff(c_229, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_209, c_224])).
% 2.64/1.35  tff(c_234, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_229])).
% 2.64/1.35  tff(c_249, plain, (![C_118, A_119, B_120]: (m1_subset_1(C_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~m2_orders_2(C_118, A_119, B_120) | ~m1_orders_1(B_120, k1_orders_1(u1_struct_0(A_119))) | ~l1_orders_2(A_119) | ~v5_orders_2(A_119) | ~v4_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.64/1.35  tff(c_251, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_249])).
% 2.64/1.35  tff(c_256, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_251])).
% 2.64/1.35  tff(c_257, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_256])).
% 2.64/1.35  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.64/1.35  tff(c_196, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 2.64/1.35  tff(c_278, plain, (![C_133, A_134, D_135, B_136]: (m1_orders_2(C_133, A_134, D_135) | m1_orders_2(D_135, A_134, C_133) | D_135=C_133 | ~m2_orders_2(D_135, A_134, B_136) | ~m2_orders_2(C_133, A_134, B_136) | ~m1_orders_1(B_136, k1_orders_1(u1_struct_0(A_134))) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.64/1.35  tff(c_280, plain, (![C_133]: (m1_orders_2(C_133, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_133) | C_133='#skF_4' | ~m2_orders_2(C_133, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_278])).
% 2.64/1.35  tff(c_285, plain, (![C_133]: (m1_orders_2(C_133, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_133) | C_133='#skF_4' | ~m2_orders_2(C_133, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_280])).
% 2.64/1.35  tff(c_304, plain, (![C_140]: (m1_orders_2(C_140, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_140) | C_140='#skF_4' | ~m2_orders_2(C_140, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_285])).
% 2.64/1.35  tff(c_310, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_304])).
% 2.64/1.35  tff(c_315, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_196, c_310])).
% 2.64/1.35  tff(c_316, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_315])).
% 2.64/1.35  tff(c_320, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_234])).
% 2.64/1.35  tff(c_330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_320])).
% 2.64/1.35  tff(c_331, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_315])).
% 2.64/1.35  tff(c_30, plain, (![C_37, B_35, A_31]: (r1_tarski(C_37, B_35) | ~m1_orders_2(C_37, A_31, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_orders_2(A_31) | ~v5_orders_2(A_31) | ~v4_orders_2(A_31) | ~v3_orders_2(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.64/1.35  tff(c_350, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_331, c_30])).
% 2.64/1.35  tff(c_361, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_257, c_350])).
% 2.64/1.35  tff(c_363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_234, c_361])).
% 2.64/1.35  tff(c_364, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_229])).
% 2.64/1.35  tff(c_368, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_195])).
% 2.64/1.35  tff(c_372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_368])).
% 2.64/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.35  
% 2.64/1.35  Inference rules
% 2.64/1.35  ----------------------
% 2.64/1.35  #Ref     : 0
% 2.64/1.35  #Sup     : 43
% 2.64/1.35  #Fact    : 0
% 2.64/1.35  #Define  : 0
% 2.64/1.35  #Split   : 5
% 2.64/1.35  #Chain   : 0
% 2.64/1.35  #Close   : 0
% 2.64/1.35  
% 2.64/1.35  Ordering : KBO
% 2.64/1.35  
% 2.64/1.35  Simplification rules
% 2.64/1.35  ----------------------
% 2.64/1.35  #Subsume      : 4
% 2.64/1.35  #Demod        : 164
% 2.64/1.35  #Tautology    : 23
% 2.64/1.35  #SimpNegUnit  : 27
% 2.64/1.35  #BackRed      : 17
% 2.64/1.35  
% 2.64/1.35  #Partial instantiations: 0
% 2.64/1.35  #Strategies tried      : 1
% 2.64/1.35  
% 2.64/1.35  Timing (in seconds)
% 2.64/1.35  ----------------------
% 2.64/1.35  Preprocessing        : 0.33
% 2.64/1.35  Parsing              : 0.18
% 2.64/1.35  CNF conversion       : 0.03
% 2.64/1.35  Main loop            : 0.25
% 2.64/1.35  Inferencing          : 0.09
% 2.64/1.35  Reduction            : 0.08
% 2.64/1.35  Demodulation         : 0.06
% 2.64/1.35  BG Simplification    : 0.02
% 2.64/1.35  Subsumption          : 0.04
% 2.64/1.35  Abstraction          : 0.01
% 2.64/1.35  MUC search           : 0.00
% 2.64/1.35  Cooper               : 0.00
% 2.64/1.36  Total                : 0.63
% 2.64/1.36  Index Insertion      : 0.00
% 2.64/1.36  Index Deletion       : 0.00
% 2.64/1.36  Index Matching       : 0.00
% 2.64/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
