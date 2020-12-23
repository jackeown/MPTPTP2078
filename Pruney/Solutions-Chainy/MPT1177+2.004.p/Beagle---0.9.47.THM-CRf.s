%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:55 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 292 expanded)
%              Number of leaves         :   37 ( 123 expanded)
%              Depth                    :   10
%              Number of atoms          :  286 (1232 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_199,negated_conjecture,(
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

tff(f_146,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_83,axiom,(
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

tff(f_102,axiom,(
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

tff(f_127,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_174,axiom,(
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

tff(c_8,plain,(
    ! [B_6] : ~ r2_xboole_0(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_48,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_46,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_44,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_42,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_40,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_38,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_177,plain,(
    ! [B_98,A_99,C_100] :
      ( r2_hidden(k1_funct_1(B_98,u1_struct_0(A_99)),C_100)
      | ~ m2_orders_2(C_100,A_99,B_98)
      | ~ m1_orders_1(B_98,k1_orders_1(u1_struct_0(A_99)))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,(
    ! [C_101,A_102,B_103] :
      ( ~ v1_xboole_0(C_101)
      | ~ m2_orders_2(C_101,A_102,B_103)
      | ~ m1_orders_1(B_103,k1_orders_1(u1_struct_0(A_102)))
      | ~ l1_orders_2(A_102)
      | ~ v5_orders_2(A_102)
      | ~ v4_orders_2(A_102)
      | ~ v3_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_177,c_2])).

tff(c_184,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_182])).

tff(c_187,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_184])).

tff(c_188,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_187])).

tff(c_163,plain,(
    ! [C_92,A_93,B_94] :
      ( m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m2_orders_2(C_92,A_93,B_94)
      | ~ m1_orders_1(B_94,k1_orders_1(u1_struct_0(A_93)))
      | ~ l1_orders_2(A_93)
      | ~ v5_orders_2(A_93)
      | ~ v4_orders_2(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_165,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_163])).

tff(c_168,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_165])).

tff(c_169,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_168])).

tff(c_36,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_116,plain,(
    ! [C_81,A_82,B_83] :
      ( m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m2_orders_2(C_81,A_82,B_83)
      | ~ m1_orders_1(B_83,k1_orders_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_118,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_116])).

tff(c_123,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_118])).

tff(c_124,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_123])).

tff(c_71,plain,(
    ! [A_71,B_72] :
      ( r2_xboole_0(A_71,B_72)
      | B_72 = A_71
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_69,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_82,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_71,c_69])).

tff(c_88,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_58,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_70,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_58])).

tff(c_109,plain,(
    ! [C_78,B_79,A_80] :
      ( r1_tarski(C_78,B_79)
      | ~ m1_orders_2(C_78,A_80,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_orders_2(A_80)
      | ~ v5_orders_2(A_80)
      | ~ v4_orders_2(A_80)
      | ~ v3_orders_2(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_111,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_109])).

tff(c_114,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_111])).

tff(c_115,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_88,c_114])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_115])).

tff(c_131,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_133,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_70])).

tff(c_189,plain,(
    ! [C_104,A_105,B_106] :
      ( ~ m1_orders_2(C_104,A_105,B_106)
      | ~ m1_orders_2(B_106,A_105,C_104)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_orders_2(A_105)
      | ~ v5_orders_2(A_105)
      | ~ v4_orders_2(A_105)
      | ~ v3_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_191,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_133,c_189])).

tff(c_194,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_169,c_133,c_191])).

tff(c_195,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_194])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_197,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_12])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_197])).

tff(c_201,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ r2_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_205,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_201,c_10])).

tff(c_221,plain,(
    ! [B_109,A_110] :
      ( B_109 = A_110
      | ~ r1_tarski(B_109,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_226,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_205,c_221])).

tff(c_231,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_246,plain,(
    ! [C_117,A_118,B_119] :
      ( m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m2_orders_2(C_117,A_118,B_119)
      | ~ m1_orders_1(B_119,k1_orders_1(u1_struct_0(A_118)))
      | ~ l1_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v4_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_250,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_246])).

tff(c_257,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_250])).

tff(c_258,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_257])).

tff(c_18,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_200,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_280,plain,(
    ! [C_136,A_137,D_138,B_139] :
      ( m1_orders_2(C_136,A_137,D_138)
      | m1_orders_2(D_138,A_137,C_136)
      | D_138 = C_136
      | ~ m2_orders_2(D_138,A_137,B_139)
      | ~ m2_orders_2(C_136,A_137,B_139)
      | ~ m1_orders_1(B_139,k1_orders_1(u1_struct_0(A_137)))
      | ~ l1_orders_2(A_137)
      | ~ v5_orders_2(A_137)
      | ~ v4_orders_2(A_137)
      | ~ v3_orders_2(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_282,plain,(
    ! [C_136] :
      ( m1_orders_2(C_136,'#skF_2','#skF_5')
      | m1_orders_2('#skF_5','#skF_2',C_136)
      | C_136 = '#skF_5'
      | ~ m2_orders_2(C_136,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_280])).

tff(c_287,plain,(
    ! [C_136] :
      ( m1_orders_2(C_136,'#skF_2','#skF_5')
      | m1_orders_2('#skF_5','#skF_2',C_136)
      | C_136 = '#skF_5'
      | ~ m2_orders_2(C_136,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_282])).

tff(c_293,plain,(
    ! [C_140] :
      ( m1_orders_2(C_140,'#skF_2','#skF_5')
      | m1_orders_2('#skF_5','#skF_2',C_140)
      | C_140 = '#skF_5'
      | ~ m2_orders_2(C_140,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_287])).

tff(c_299,plain,
    ( m1_orders_2('#skF_4','#skF_2','#skF_5')
    | m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_293])).

tff(c_304,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_299])).

tff(c_305,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_322,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_231])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_322])).

tff(c_332,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_26,plain,(
    ! [C_23,B_21,A_17] :
      ( r1_tarski(C_23,B_21)
      | ~ m1_orders_2(C_23,A_17,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_orders_2(A_17)
      | ~ v5_orders_2(A_17)
      | ~ v4_orders_2(A_17)
      | ~ v3_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_341,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_332,c_26])).

tff(c_356,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_258,c_341])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_231,c_356])).

tff(c_359,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_363,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_201])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.34  
% 2.51/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.34  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.51/1.34  
% 2.51/1.34  %Foreground sorts:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Background operators:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Foreground operators:
% 2.51/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.51/1.34  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.51/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.34  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.51/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.34  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.51/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.34  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.51/1.34  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.51/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.34  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.51/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.51/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.51/1.34  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.34  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.51/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.34  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.51/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.51/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.34  
% 2.51/1.36  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.51/1.36  tff(f_199, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 2.51/1.36  tff(f_146, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.51/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.51/1.36  tff(f_83, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.51/1.36  tff(f_102, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 2.51/1.36  tff(f_127, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 2.51/1.36  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.51/1.36  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.51/1.36  tff(f_174, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 2.51/1.36  tff(c_8, plain, (![B_6]: (~r2_xboole_0(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.51/1.36  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.51/1.36  tff(c_48, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.51/1.36  tff(c_46, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.51/1.36  tff(c_44, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.51/1.36  tff(c_42, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.51/1.36  tff(c_40, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.51/1.36  tff(c_38, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.51/1.36  tff(c_177, plain, (![B_98, A_99, C_100]: (r2_hidden(k1_funct_1(B_98, u1_struct_0(A_99)), C_100) | ~m2_orders_2(C_100, A_99, B_98) | ~m1_orders_1(B_98, k1_orders_1(u1_struct_0(A_99))) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.51/1.36  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.36  tff(c_182, plain, (![C_101, A_102, B_103]: (~v1_xboole_0(C_101) | ~m2_orders_2(C_101, A_102, B_103) | ~m1_orders_1(B_103, k1_orders_1(u1_struct_0(A_102))) | ~l1_orders_2(A_102) | ~v5_orders_2(A_102) | ~v4_orders_2(A_102) | ~v3_orders_2(A_102) | v2_struct_0(A_102))), inference(resolution, [status(thm)], [c_177, c_2])).
% 2.51/1.36  tff(c_184, plain, (~v1_xboole_0('#skF_4') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_182])).
% 2.51/1.36  tff(c_187, plain, (~v1_xboole_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_184])).
% 2.51/1.36  tff(c_188, plain, (~v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_187])).
% 2.51/1.36  tff(c_163, plain, (![C_92, A_93, B_94]: (m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~m2_orders_2(C_92, A_93, B_94) | ~m1_orders_1(B_94, k1_orders_1(u1_struct_0(A_93))) | ~l1_orders_2(A_93) | ~v5_orders_2(A_93) | ~v4_orders_2(A_93) | ~v3_orders_2(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.51/1.36  tff(c_165, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_163])).
% 2.51/1.36  tff(c_168, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_165])).
% 2.51/1.36  tff(c_169, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_168])).
% 2.51/1.36  tff(c_36, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.51/1.36  tff(c_116, plain, (![C_81, A_82, B_83]: (m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~m2_orders_2(C_81, A_82, B_83) | ~m1_orders_1(B_83, k1_orders_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.51/1.36  tff(c_118, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_116])).
% 2.51/1.36  tff(c_123, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_118])).
% 2.51/1.36  tff(c_124, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_123])).
% 2.51/1.36  tff(c_71, plain, (![A_71, B_72]: (r2_xboole_0(A_71, B_72) | B_72=A_71 | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.51/1.36  tff(c_52, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.51/1.36  tff(c_69, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 2.51/1.36  tff(c_82, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_71, c_69])).
% 2.51/1.36  tff(c_88, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_82])).
% 2.51/1.36  tff(c_58, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_199])).
% 2.51/1.36  tff(c_70, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_69, c_58])).
% 2.51/1.36  tff(c_109, plain, (![C_78, B_79, A_80]: (r1_tarski(C_78, B_79) | ~m1_orders_2(C_78, A_80, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_orders_2(A_80) | ~v5_orders_2(A_80) | ~v4_orders_2(A_80) | ~v3_orders_2(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.51/1.36  tff(c_111, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_109])).
% 2.51/1.36  tff(c_114, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_111])).
% 2.51/1.36  tff(c_115, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_88, c_114])).
% 2.51/1.36  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_115])).
% 2.51/1.36  tff(c_131, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_82])).
% 2.51/1.36  tff(c_133, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_70])).
% 2.51/1.36  tff(c_189, plain, (![C_104, A_105, B_106]: (~m1_orders_2(C_104, A_105, B_106) | ~m1_orders_2(B_106, A_105, C_104) | k1_xboole_0=B_106 | ~m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_orders_2(A_105) | ~v5_orders_2(A_105) | ~v4_orders_2(A_105) | ~v3_orders_2(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.51/1.36  tff(c_191, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_133, c_189])).
% 2.51/1.36  tff(c_194, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_169, c_133, c_191])).
% 2.51/1.36  tff(c_195, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_194])).
% 2.51/1.36  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.51/1.36  tff(c_197, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_12])).
% 2.51/1.36  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_197])).
% 2.51/1.36  tff(c_201, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 2.51/1.36  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~r2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.51/1.36  tff(c_205, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_201, c_10])).
% 2.51/1.36  tff(c_221, plain, (![B_109, A_110]: (B_109=A_110 | ~r1_tarski(B_109, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.36  tff(c_226, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_205, c_221])).
% 2.51/1.36  tff(c_231, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_226])).
% 2.51/1.36  tff(c_246, plain, (![C_117, A_118, B_119]: (m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~m2_orders_2(C_117, A_118, B_119) | ~m1_orders_1(B_119, k1_orders_1(u1_struct_0(A_118))) | ~l1_orders_2(A_118) | ~v5_orders_2(A_118) | ~v4_orders_2(A_118) | ~v3_orders_2(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.51/1.36  tff(c_250, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_246])).
% 2.51/1.36  tff(c_257, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_250])).
% 2.51/1.36  tff(c_258, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_257])).
% 2.51/1.36  tff(c_18, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.36  tff(c_200, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 2.51/1.36  tff(c_280, plain, (![C_136, A_137, D_138, B_139]: (m1_orders_2(C_136, A_137, D_138) | m1_orders_2(D_138, A_137, C_136) | D_138=C_136 | ~m2_orders_2(D_138, A_137, B_139) | ~m2_orders_2(C_136, A_137, B_139) | ~m1_orders_1(B_139, k1_orders_1(u1_struct_0(A_137))) | ~l1_orders_2(A_137) | ~v5_orders_2(A_137) | ~v4_orders_2(A_137) | ~v3_orders_2(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_174])).
% 2.51/1.36  tff(c_282, plain, (![C_136]: (m1_orders_2(C_136, '#skF_2', '#skF_5') | m1_orders_2('#skF_5', '#skF_2', C_136) | C_136='#skF_5' | ~m2_orders_2(C_136, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_280])).
% 2.51/1.36  tff(c_287, plain, (![C_136]: (m1_orders_2(C_136, '#skF_2', '#skF_5') | m1_orders_2('#skF_5', '#skF_2', C_136) | C_136='#skF_5' | ~m2_orders_2(C_136, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_282])).
% 2.51/1.36  tff(c_293, plain, (![C_140]: (m1_orders_2(C_140, '#skF_2', '#skF_5') | m1_orders_2('#skF_5', '#skF_2', C_140) | C_140='#skF_5' | ~m2_orders_2(C_140, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_287])).
% 2.51/1.36  tff(c_299, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5') | m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_293])).
% 2.51/1.36  tff(c_304, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_200, c_299])).
% 2.51/1.36  tff(c_305, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_304])).
% 2.51/1.36  tff(c_322, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_231])).
% 2.51/1.36  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_322])).
% 2.51/1.36  tff(c_332, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_304])).
% 2.51/1.36  tff(c_26, plain, (![C_23, B_21, A_17]: (r1_tarski(C_23, B_21) | ~m1_orders_2(C_23, A_17, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_orders_2(A_17) | ~v5_orders_2(A_17) | ~v4_orders_2(A_17) | ~v3_orders_2(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.51/1.36  tff(c_341, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_332, c_26])).
% 2.51/1.36  tff(c_356, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_258, c_341])).
% 2.51/1.36  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_231, c_356])).
% 2.51/1.36  tff(c_359, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_226])).
% 2.51/1.36  tff(c_363, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_201])).
% 2.51/1.36  tff(c_367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_363])).
% 2.51/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  Inference rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Ref     : 0
% 2.51/1.36  #Sup     : 42
% 2.51/1.36  #Fact    : 0
% 2.51/1.36  #Define  : 0
% 2.51/1.36  #Split   : 4
% 2.51/1.36  #Chain   : 0
% 2.51/1.36  #Close   : 0
% 2.51/1.36  
% 2.51/1.36  Ordering : KBO
% 2.51/1.36  
% 2.51/1.36  Simplification rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Subsume      : 5
% 2.51/1.36  #Demod        : 152
% 2.51/1.36  #Tautology    : 24
% 2.51/1.36  #SimpNegUnit  : 29
% 2.51/1.36  #BackRed      : 18
% 2.51/1.36  
% 2.51/1.36  #Partial instantiations: 0
% 2.51/1.36  #Strategies tried      : 1
% 2.51/1.36  
% 2.51/1.36  Timing (in seconds)
% 2.51/1.36  ----------------------
% 2.73/1.36  Preprocessing        : 0.32
% 2.73/1.36  Parsing              : 0.17
% 2.73/1.36  CNF conversion       : 0.03
% 2.73/1.36  Main loop            : 0.25
% 2.73/1.36  Inferencing          : 0.09
% 2.73/1.36  Reduction            : 0.08
% 2.73/1.36  Demodulation         : 0.06
% 2.73/1.36  BG Simplification    : 0.02
% 2.73/1.36  Subsumption          : 0.04
% 2.73/1.37  Abstraction          : 0.01
% 2.73/1.37  MUC search           : 0.00
% 2.73/1.37  Cooper               : 0.00
% 2.73/1.37  Total                : 0.60
% 2.73/1.37  Index Insertion      : 0.00
% 2.73/1.37  Index Deletion       : 0.00
% 2.73/1.37  Index Matching       : 0.00
% 2.73/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
