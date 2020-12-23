%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:59 EST 2020

% Result     : Theorem 10.72s
% Output     : CNFRefutation 10.86s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 417 expanded)
%              Number of leaves         :   37 ( 166 expanded)
%              Depth                    :   15
%              Number of atoms          :  315 (1783 expanded)
%              Number of equality atoms :   33 (  88 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_216,negated_conjecture,(
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

tff(f_100,axiom,(
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

tff(f_119,axiom,(
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

tff(f_144,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

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
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_191,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_58,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_123,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_42,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_54,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_52,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_50,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_48,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_46,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_769,plain,(
    ! [C_162,A_163,B_164] :
      ( m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ m2_orders_2(C_162,A_163,B_164)
      | ~ m1_orders_1(B_164,k1_orders_1(u1_struct_0(A_163)))
      | ~ l1_orders_2(A_163)
      | ~ v5_orders_2(A_163)
      | ~ v4_orders_2(A_163)
      | ~ v3_orders_2(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_771,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_769])).

tff(c_774,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_771])).

tff(c_775,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_774])).

tff(c_244,plain,(
    ! [A_96,B_97] :
      ( r2_xboole_0(A_96,B_97)
      | B_97 = A_96
      | ~ r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_255,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_244,c_123])).

tff(c_261,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_64,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_124,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_465,plain,(
    ! [C_118,B_119,A_120] :
      ( r1_tarski(C_118,B_119)
      | ~ m1_orders_2(C_118,A_120,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_orders_2(A_120)
      | ~ v5_orders_2(A_120)
      | ~ v4_orders_2(A_120)
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_467,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_124,c_465])).

tff(c_470,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_467])).

tff(c_471,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_261,c_470])).

tff(c_493,plain,(
    ! [C_126,A_127,B_128] :
      ( m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m2_orders_2(C_126,A_127,B_128)
      | ~ m1_orders_1(B_128,k1_orders_1(u1_struct_0(A_127)))
      | ~ l1_orders_2(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v4_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_497,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_493])).

tff(c_504,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_497])).

tff(c_506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_471,c_504])).

tff(c_507,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_509,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_124])).

tff(c_4555,plain,(
    ! [C_1374,A_1375,B_1376] :
      ( ~ m1_orders_2(C_1374,A_1375,B_1376)
      | ~ m1_orders_2(B_1376,A_1375,C_1374)
      | k1_xboole_0 = B_1376
      | ~ m1_subset_1(C_1374,k1_zfmisc_1(u1_struct_0(A_1375)))
      | ~ m1_subset_1(B_1376,k1_zfmisc_1(u1_struct_0(A_1375)))
      | ~ l1_orders_2(A_1375)
      | ~ v5_orders_2(A_1375)
      | ~ v4_orders_2(A_1375)
      | ~ v3_orders_2(A_1375)
      | v2_struct_0(A_1375) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4577,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_509,c_4555])).

tff(c_4580,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_775,c_509,c_4577])).

tff(c_4581,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4580])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_83,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_95,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_83])).

tff(c_169,plain,(
    ! [A_89,C_90,B_91] :
      ( r1_tarski(k4_xboole_0(A_89,C_90),B_91)
      | ~ r1_tarski(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_188,plain,(
    ! [B_92,B_93] :
      ( r1_tarski(k1_xboole_0,B_92)
      | ~ r1_tarski(B_93,B_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_169])).

tff(c_203,plain,(
    ! [B_94] : r1_tarski(k1_xboole_0,B_94) ),
    inference(resolution,[status(thm)],[c_12,c_188])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_216,plain,(
    ! [B_94] : k4_xboole_0(k1_xboole_0,B_94) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_203,c_16])).

tff(c_4603,plain,(
    ! [B_94] : k4_xboole_0('#skF_4',B_94) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4581,c_4581,c_216])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4609,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4581,c_14])).

tff(c_3170,plain,(
    ! [B_911,A_912,C_913] :
      ( r2_hidden(k1_funct_1(B_911,u1_struct_0(A_912)),C_913)
      | ~ m2_orders_2(C_913,A_912,B_911)
      | ~ m1_orders_1(B_911,k1_orders_1(u1_struct_0(A_912)))
      | ~ l1_orders_2(A_912)
      | ~ v5_orders_2(A_912)
      | ~ v4_orders_2(A_912)
      | ~ v3_orders_2(A_912)
      | v2_struct_0(A_912) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_7687,plain,(
    ! [C_2188,B_2189,A_2190] :
      ( ~ r1_tarski(C_2188,k1_funct_1(B_2189,u1_struct_0(A_2190)))
      | ~ m2_orders_2(C_2188,A_2190,B_2189)
      | ~ m1_orders_1(B_2189,k1_orders_1(u1_struct_0(A_2190)))
      | ~ l1_orders_2(A_2190)
      | ~ v5_orders_2(A_2190)
      | ~ v4_orders_2(A_2190)
      | ~ v3_orders_2(A_2190)
      | v2_struct_0(A_2190) ) ),
    inference(resolution,[status(thm)],[c_3170,c_24])).

tff(c_32447,plain,(
    ! [A_8463,A_8464,B_8465] :
      ( ~ m2_orders_2(A_8463,A_8464,B_8465)
      | ~ m1_orders_1(B_8465,k1_orders_1(u1_struct_0(A_8464)))
      | ~ l1_orders_2(A_8464)
      | ~ v5_orders_2(A_8464)
      | ~ v4_orders_2(A_8464)
      | ~ v3_orders_2(A_8464)
      | v2_struct_0(A_8464)
      | k4_xboole_0(A_8463,k1_funct_1(B_8465,u1_struct_0(A_8464))) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_4609,c_7687])).

tff(c_32485,plain,(
    ! [A_8463] :
      ( ~ m2_orders_2(A_8463,'#skF_1','#skF_2')
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1')
      | k4_xboole_0(A_8463,k1_funct_1('#skF_2',u1_struct_0('#skF_1'))) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_46,c_32447])).

tff(c_32488,plain,(
    ! [A_8463] :
      ( ~ m2_orders_2(A_8463,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1')
      | k4_xboole_0(A_8463,k1_funct_1('#skF_2',u1_struct_0('#skF_1'))) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_32485])).

tff(c_32490,plain,(
    ! [A_8508] :
      ( ~ m2_orders_2(A_8508,'#skF_1','#skF_2')
      | k4_xboole_0(A_8508,k1_funct_1('#skF_2',u1_struct_0('#skF_1'))) != '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_32488])).

tff(c_32590,plain,(
    ~ m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4603,c_32490])).

tff(c_32602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32590])).

tff(c_32603,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_32605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_32603])).

tff(c_32607,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32623,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32607,c_6])).

tff(c_32646,plain,(
    ! [B_8553,A_8554] :
      ( B_8553 = A_8554
      | ~ r1_tarski(B_8553,A_8554)
      | ~ r1_tarski(A_8554,B_8553) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32655,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32623,c_32646])).

tff(c_32662,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32655])).

tff(c_44,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_33041,plain,(
    ! [C_8590,A_8591,B_8592] :
      ( m1_subset_1(C_8590,k1_zfmisc_1(u1_struct_0(A_8591)))
      | ~ m2_orders_2(C_8590,A_8591,B_8592)
      | ~ m1_orders_1(B_8592,k1_orders_1(u1_struct_0(A_8591)))
      | ~ l1_orders_2(A_8591)
      | ~ v5_orders_2(A_8591)
      | ~ v4_orders_2(A_8591)
      | ~ v3_orders_2(A_8591)
      | v2_struct_0(A_8591) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_33043,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_33041])).

tff(c_33048,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_33043])).

tff(c_33049,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_33048])).

tff(c_32606,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_36309,plain,(
    ! [C_9537,A_9538,D_9539,B_9540] :
      ( m1_orders_2(C_9537,A_9538,D_9539)
      | m1_orders_2(D_9539,A_9538,C_9537)
      | D_9539 = C_9537
      | ~ m2_orders_2(D_9539,A_9538,B_9540)
      | ~ m2_orders_2(C_9537,A_9538,B_9540)
      | ~ m1_orders_1(B_9540,k1_orders_1(u1_struct_0(A_9538)))
      | ~ l1_orders_2(A_9538)
      | ~ v5_orders_2(A_9538)
      | ~ v4_orders_2(A_9538)
      | ~ v3_orders_2(A_9538)
      | v2_struct_0(A_9538) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_36311,plain,(
    ! [C_9537] :
      ( m1_orders_2(C_9537,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_9537)
      | C_9537 = '#skF_3'
      | ~ m2_orders_2(C_9537,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_36309])).

tff(c_36316,plain,(
    ! [C_9537] :
      ( m1_orders_2(C_9537,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_9537)
      | C_9537 = '#skF_3'
      | ~ m2_orders_2(C_9537,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_36311])).

tff(c_37877,plain,(
    ! [C_10190] :
      ( m1_orders_2(C_10190,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_10190)
      | C_10190 = '#skF_3'
      | ~ m2_orders_2(C_10190,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_36316])).

tff(c_37987,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_37877])).

tff(c_37992,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_32606,c_37987])).

tff(c_37993,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_37992])).

tff(c_38036,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37993,c_32662])).

tff(c_38044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38036])).

tff(c_38045,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_37992])).

tff(c_32,plain,(
    ! [C_30,B_28,A_24] :
      ( r1_tarski(C_30,B_28)
      | ~ m1_orders_2(C_30,A_24,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_orders_2(A_24)
      | ~ v5_orders_2(A_24)
      | ~ v4_orders_2(A_24)
      | ~ v3_orders_2(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38172,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38045,c_32])).

tff(c_38253,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_33049,c_38172])).

tff(c_38255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_32662,c_38253])).

tff(c_38256,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32655])).

tff(c_38261,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38256,c_32607])).

tff(c_38266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_38261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.72/4.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.72/4.07  
% 10.72/4.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.72/4.07  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.72/4.07  
% 10.72/4.07  %Foreground sorts:
% 10.72/4.07  
% 10.72/4.07  
% 10.72/4.07  %Background operators:
% 10.72/4.07  
% 10.72/4.07  
% 10.72/4.07  %Foreground operators:
% 10.72/4.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.72/4.07  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 10.72/4.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.72/4.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.72/4.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.72/4.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.72/4.07  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 10.72/4.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.72/4.07  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 10.72/4.07  tff('#skF_2', type, '#skF_2': $i).
% 10.72/4.07  tff('#skF_3', type, '#skF_3': $i).
% 10.72/4.07  tff('#skF_1', type, '#skF_1': $i).
% 10.72/4.07  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 10.72/4.07  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 10.72/4.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.72/4.07  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 10.72/4.07  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.72/4.07  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.72/4.07  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 10.72/4.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.72/4.07  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 10.72/4.07  tff('#skF_4', type, '#skF_4': $i).
% 10.72/4.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.72/4.07  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 10.72/4.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.72/4.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.72/4.07  
% 10.86/4.09  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 10.86/4.09  tff(f_216, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_orders_2)).
% 10.86/4.09  tff(f_100, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 10.86/4.09  tff(f_119, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 10.86/4.09  tff(f_144, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 10.86/4.09  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.86/4.09  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.86/4.09  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 10.86/4.09  tff(f_163, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 10.86/4.09  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 10.86/4.09  tff(f_191, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_orders_2)).
% 10.86/4.09  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.86/4.09  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 10.86/4.09  tff(c_58, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 10.86/4.09  tff(c_123, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 10.86/4.09  tff(c_42, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 10.86/4.09  tff(c_54, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 10.86/4.09  tff(c_52, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 10.86/4.09  tff(c_50, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 10.86/4.09  tff(c_48, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 10.86/4.09  tff(c_46, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 10.86/4.09  tff(c_769, plain, (![C_162, A_163, B_164]: (m1_subset_1(C_162, k1_zfmisc_1(u1_struct_0(A_163))) | ~m2_orders_2(C_162, A_163, B_164) | ~m1_orders_1(B_164, k1_orders_1(u1_struct_0(A_163))) | ~l1_orders_2(A_163) | ~v5_orders_2(A_163) | ~v4_orders_2(A_163) | ~v3_orders_2(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.86/4.09  tff(c_771, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_769])).
% 10.86/4.09  tff(c_774, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_771])).
% 10.86/4.09  tff(c_775, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_774])).
% 10.86/4.09  tff(c_244, plain, (![A_96, B_97]: (r2_xboole_0(A_96, B_97) | B_97=A_96 | ~r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.86/4.09  tff(c_255, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_244, c_123])).
% 10.86/4.09  tff(c_261, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_255])).
% 10.86/4.09  tff(c_64, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 10.86/4.09  tff(c_124, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 10.86/4.09  tff(c_465, plain, (![C_118, B_119, A_120]: (r1_tarski(C_118, B_119) | ~m1_orders_2(C_118, A_120, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_orders_2(A_120) | ~v5_orders_2(A_120) | ~v4_orders_2(A_120) | ~v3_orders_2(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.86/4.09  tff(c_467, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_124, c_465])).
% 10.86/4.09  tff(c_470, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_467])).
% 10.86/4.09  tff(c_471, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_261, c_470])).
% 10.86/4.09  tff(c_493, plain, (![C_126, A_127, B_128]: (m1_subset_1(C_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~m2_orders_2(C_126, A_127, B_128) | ~m1_orders_1(B_128, k1_orders_1(u1_struct_0(A_127))) | ~l1_orders_2(A_127) | ~v5_orders_2(A_127) | ~v4_orders_2(A_127) | ~v3_orders_2(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.86/4.09  tff(c_497, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_493])).
% 10.86/4.09  tff(c_504, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_497])).
% 10.86/4.09  tff(c_506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_471, c_504])).
% 10.86/4.09  tff(c_507, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_255])).
% 10.86/4.09  tff(c_509, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_507, c_124])).
% 10.86/4.09  tff(c_4555, plain, (![C_1374, A_1375, B_1376]: (~m1_orders_2(C_1374, A_1375, B_1376) | ~m1_orders_2(B_1376, A_1375, C_1374) | k1_xboole_0=B_1376 | ~m1_subset_1(C_1374, k1_zfmisc_1(u1_struct_0(A_1375))) | ~m1_subset_1(B_1376, k1_zfmisc_1(u1_struct_0(A_1375))) | ~l1_orders_2(A_1375) | ~v5_orders_2(A_1375) | ~v4_orders_2(A_1375) | ~v3_orders_2(A_1375) | v2_struct_0(A_1375))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.86/4.09  tff(c_4577, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_509, c_4555])).
% 10.86/4.09  tff(c_4580, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_775, c_509, c_4577])).
% 10.86/4.09  tff(c_4581, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_4580])).
% 10.86/4.09  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.86/4.09  tff(c_83, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k1_xboole_0 | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.86/4.09  tff(c_95, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_83])).
% 10.86/4.09  tff(c_169, plain, (![A_89, C_90, B_91]: (r1_tarski(k4_xboole_0(A_89, C_90), B_91) | ~r1_tarski(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.86/4.09  tff(c_188, plain, (![B_92, B_93]: (r1_tarski(k1_xboole_0, B_92) | ~r1_tarski(B_93, B_92))), inference(superposition, [status(thm), theory('equality')], [c_95, c_169])).
% 10.86/4.09  tff(c_203, plain, (![B_94]: (r1_tarski(k1_xboole_0, B_94))), inference(resolution, [status(thm)], [c_12, c_188])).
% 10.86/4.09  tff(c_16, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.86/4.09  tff(c_216, plain, (![B_94]: (k4_xboole_0(k1_xboole_0, B_94)=k1_xboole_0)), inference(resolution, [status(thm)], [c_203, c_16])).
% 10.86/4.09  tff(c_4603, plain, (![B_94]: (k4_xboole_0('#skF_4', B_94)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4581, c_4581, c_216])).
% 10.86/4.09  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.86/4.09  tff(c_4609, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4581, c_14])).
% 10.86/4.09  tff(c_3170, plain, (![B_911, A_912, C_913]: (r2_hidden(k1_funct_1(B_911, u1_struct_0(A_912)), C_913) | ~m2_orders_2(C_913, A_912, B_911) | ~m1_orders_1(B_911, k1_orders_1(u1_struct_0(A_912))) | ~l1_orders_2(A_912) | ~v5_orders_2(A_912) | ~v4_orders_2(A_912) | ~v3_orders_2(A_912) | v2_struct_0(A_912))), inference(cnfTransformation, [status(thm)], [f_163])).
% 10.86/4.09  tff(c_24, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.86/4.09  tff(c_7687, plain, (![C_2188, B_2189, A_2190]: (~r1_tarski(C_2188, k1_funct_1(B_2189, u1_struct_0(A_2190))) | ~m2_orders_2(C_2188, A_2190, B_2189) | ~m1_orders_1(B_2189, k1_orders_1(u1_struct_0(A_2190))) | ~l1_orders_2(A_2190) | ~v5_orders_2(A_2190) | ~v4_orders_2(A_2190) | ~v3_orders_2(A_2190) | v2_struct_0(A_2190))), inference(resolution, [status(thm)], [c_3170, c_24])).
% 10.86/4.09  tff(c_32447, plain, (![A_8463, A_8464, B_8465]: (~m2_orders_2(A_8463, A_8464, B_8465) | ~m1_orders_1(B_8465, k1_orders_1(u1_struct_0(A_8464))) | ~l1_orders_2(A_8464) | ~v5_orders_2(A_8464) | ~v4_orders_2(A_8464) | ~v3_orders_2(A_8464) | v2_struct_0(A_8464) | k4_xboole_0(A_8463, k1_funct_1(B_8465, u1_struct_0(A_8464)))!='#skF_4')), inference(resolution, [status(thm)], [c_4609, c_7687])).
% 10.86/4.09  tff(c_32485, plain, (![A_8463]: (~m2_orders_2(A_8463, '#skF_1', '#skF_2') | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1') | k4_xboole_0(A_8463, k1_funct_1('#skF_2', u1_struct_0('#skF_1')))!='#skF_4')), inference(resolution, [status(thm)], [c_46, c_32447])).
% 10.86/4.09  tff(c_32488, plain, (![A_8463]: (~m2_orders_2(A_8463, '#skF_1', '#skF_2') | v2_struct_0('#skF_1') | k4_xboole_0(A_8463, k1_funct_1('#skF_2', u1_struct_0('#skF_1')))!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_32485])).
% 10.86/4.09  tff(c_32490, plain, (![A_8508]: (~m2_orders_2(A_8508, '#skF_1', '#skF_2') | k4_xboole_0(A_8508, k1_funct_1('#skF_2', u1_struct_0('#skF_1')))!='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_32488])).
% 10.86/4.09  tff(c_32590, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4603, c_32490])).
% 10.86/4.09  tff(c_32602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_32590])).
% 10.86/4.09  tff(c_32603, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_64])).
% 10.86/4.09  tff(c_32605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_32603])).
% 10.86/4.09  tff(c_32607, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 10.86/4.09  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.86/4.09  tff(c_32623, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32607, c_6])).
% 10.86/4.09  tff(c_32646, plain, (![B_8553, A_8554]: (B_8553=A_8554 | ~r1_tarski(B_8553, A_8554) | ~r1_tarski(A_8554, B_8553))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.86/4.09  tff(c_32655, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32623, c_32646])).
% 10.86/4.09  tff(c_32662, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_32655])).
% 10.86/4.09  tff(c_44, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 10.86/4.09  tff(c_33041, plain, (![C_8590, A_8591, B_8592]: (m1_subset_1(C_8590, k1_zfmisc_1(u1_struct_0(A_8591))) | ~m2_orders_2(C_8590, A_8591, B_8592) | ~m1_orders_1(B_8592, k1_orders_1(u1_struct_0(A_8591))) | ~l1_orders_2(A_8591) | ~v5_orders_2(A_8591) | ~v4_orders_2(A_8591) | ~v3_orders_2(A_8591) | v2_struct_0(A_8591))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.86/4.09  tff(c_33043, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_33041])).
% 10.86/4.09  tff(c_33048, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_33043])).
% 10.86/4.09  tff(c_33049, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_33048])).
% 10.86/4.09  tff(c_32606, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 10.86/4.09  tff(c_36309, plain, (![C_9537, A_9538, D_9539, B_9540]: (m1_orders_2(C_9537, A_9538, D_9539) | m1_orders_2(D_9539, A_9538, C_9537) | D_9539=C_9537 | ~m2_orders_2(D_9539, A_9538, B_9540) | ~m2_orders_2(C_9537, A_9538, B_9540) | ~m1_orders_1(B_9540, k1_orders_1(u1_struct_0(A_9538))) | ~l1_orders_2(A_9538) | ~v5_orders_2(A_9538) | ~v4_orders_2(A_9538) | ~v3_orders_2(A_9538) | v2_struct_0(A_9538))), inference(cnfTransformation, [status(thm)], [f_191])).
% 10.86/4.09  tff(c_36311, plain, (![C_9537]: (m1_orders_2(C_9537, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_9537) | C_9537='#skF_3' | ~m2_orders_2(C_9537, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_36309])).
% 10.86/4.09  tff(c_36316, plain, (![C_9537]: (m1_orders_2(C_9537, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_9537) | C_9537='#skF_3' | ~m2_orders_2(C_9537, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_36311])).
% 10.86/4.09  tff(c_37877, plain, (![C_10190]: (m1_orders_2(C_10190, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_10190) | C_10190='#skF_3' | ~m2_orders_2(C_10190, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_36316])).
% 10.86/4.09  tff(c_37987, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_42, c_37877])).
% 10.86/4.09  tff(c_37992, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_32606, c_37987])).
% 10.86/4.09  tff(c_37993, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_37992])).
% 10.86/4.09  tff(c_38036, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37993, c_32662])).
% 10.86/4.09  tff(c_38044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_38036])).
% 10.86/4.09  tff(c_38045, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_37992])).
% 10.86/4.09  tff(c_32, plain, (![C_30, B_28, A_24]: (r1_tarski(C_30, B_28) | ~m1_orders_2(C_30, A_24, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_orders_2(A_24) | ~v5_orders_2(A_24) | ~v4_orders_2(A_24) | ~v3_orders_2(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.86/4.09  tff(c_38172, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38045, c_32])).
% 10.86/4.09  tff(c_38253, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_33049, c_38172])).
% 10.86/4.09  tff(c_38255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_32662, c_38253])).
% 10.86/4.09  tff(c_38256, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_32655])).
% 10.86/4.09  tff(c_38261, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38256, c_32607])).
% 10.86/4.09  tff(c_38266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_38261])).
% 10.86/4.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.86/4.09  
% 10.86/4.09  Inference rules
% 10.86/4.09  ----------------------
% 10.86/4.09  #Ref     : 0
% 10.86/4.09  #Sup     : 5624
% 10.86/4.09  #Fact    : 18
% 10.86/4.09  #Define  : 0
% 10.86/4.09  #Split   : 42
% 10.86/4.09  #Chain   : 0
% 10.86/4.09  #Close   : 0
% 10.86/4.09  
% 10.86/4.09  Ordering : KBO
% 10.86/4.09  
% 10.86/4.09  Simplification rules
% 10.86/4.09  ----------------------
% 10.86/4.09  #Subsume      : 3096
% 10.86/4.09  #Demod        : 2160
% 10.86/4.09  #Tautology    : 1089
% 10.86/4.09  #SimpNegUnit  : 604
% 10.86/4.09  #BackRed      : 94
% 10.86/4.09  
% 10.86/4.09  #Partial instantiations: 13710
% 10.86/4.09  #Strategies tried      : 1
% 10.86/4.09  
% 10.86/4.09  Timing (in seconds)
% 10.86/4.09  ----------------------
% 10.86/4.10  Preprocessing        : 0.37
% 10.86/4.10  Parsing              : 0.20
% 10.86/4.10  CNF conversion       : 0.03
% 10.86/4.10  Main loop            : 2.88
% 10.86/4.10  Inferencing          : 0.78
% 10.86/4.10  Reduction            : 0.71
% 10.86/4.10  Demodulation         : 0.45
% 10.86/4.10  BG Simplification    : 0.06
% 10.86/4.10  Subsumption          : 1.19
% 10.86/4.10  Abstraction          : 0.09
% 10.86/4.10  MUC search           : 0.00
% 10.86/4.10  Cooper               : 0.00
% 10.86/4.10  Total                : 3.29
% 10.86/4.10  Index Insertion      : 0.00
% 10.86/4.10  Index Deletion       : 0.00
% 10.86/4.10  Index Matching       : 0.00
% 10.86/4.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
