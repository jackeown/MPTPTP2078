%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:00 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 299 expanded)
%              Number of leaves         :   38 ( 126 expanded)
%              Depth                    :   10
%              Number of atoms          :  293 (1253 expanded)
%              Number of equality atoms :   24 (  50 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_220,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_167,axiom,(
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
                 => ~ r1_xboole_0(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

tff(f_195,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_44,plain,(
    m2_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_54,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_52,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_50,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_48,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_46,plain,(
    m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_364,plain,(
    ! [C_155,A_156,B_157] :
      ( m1_subset_1(C_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m2_orders_2(C_155,A_156,B_157)
      | ~ m1_orders_1(B_157,k1_orders_1(u1_struct_0(A_156)))
      | ~ l1_orders_2(A_156)
      | ~ v5_orders_2(A_156)
      | ~ v4_orders_2(A_156)
      | ~ v3_orders_2(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_366,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_364])).

tff(c_369,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_366])).

tff(c_370,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_369])).

tff(c_105,plain,(
    ! [A_90,B_91] :
      ( r2_xboole_0(A_90,B_91)
      | B_91 = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_5')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_72,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_116,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_105,c_72])).

tff(c_137,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_64,plain,
    ( r2_xboole_0('#skF_4','#skF_5')
    | m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_73,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_64])).

tff(c_168,plain,(
    ! [C_106,B_107,A_108] :
      ( r1_tarski(C_106,B_107)
      | ~ m1_orders_2(C_106,A_108,B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_orders_2(A_108)
      | ~ v5_orders_2(A_108)
      | ~ v4_orders_2(A_108)
      | ~ v3_orders_2(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_170,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_168])).

tff(c_173,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_170])).

tff(c_174,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_137,c_173])).

tff(c_42,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_227,plain,(
    ! [C_119,A_120,B_121] :
      ( m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m2_orders_2(C_119,A_120,B_121)
      | ~ m1_orders_1(B_121,k1_orders_1(u1_struct_0(A_120)))
      | ~ l1_orders_2(A_120)
      | ~ v5_orders_2(A_120)
      | ~ v4_orders_2(A_120)
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_231,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_227])).

tff(c_238,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_231])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_174,c_238])).

tff(c_241,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_243,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_73])).

tff(c_412,plain,(
    ! [C_171,A_172,B_173] :
      ( ~ m1_orders_2(C_171,A_172,B_173)
      | ~ m1_orders_2(B_173,A_172,C_171)
      | k1_xboole_0 = B_173
      | ~ m1_subset_1(C_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_orders_2(A_172)
      | ~ v5_orders_2(A_172)
      | ~ v4_orders_2(A_172)
      | ~ v3_orders_2(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_414,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_243,c_412])).

tff(c_417,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_370,c_243,c_414])).

tff(c_418,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_417])).

tff(c_22,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_87,plain,(
    ! [A_89] :
      ( k1_xboole_0 = A_89
      | ~ r1_tarski(A_89,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_122,plain,(
    ! [B_92] : k4_xboole_0(k1_xboole_0,B_92) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_87])).

tff(c_24,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_127,plain,(
    ! [B_92] : r1_xboole_0(k1_xboole_0,B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_24])).

tff(c_392,plain,(
    ! [C_164,D_165,A_166,B_167] :
      ( ~ r1_xboole_0(C_164,D_165)
      | ~ m2_orders_2(D_165,A_166,B_167)
      | ~ m2_orders_2(C_164,A_166,B_167)
      | ~ m1_orders_1(B_167,k1_orders_1(u1_struct_0(A_166)))
      | ~ l1_orders_2(A_166)
      | ~ v5_orders_2(A_166)
      | ~ v4_orders_2(A_166)
      | ~ v3_orders_2(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_405,plain,(
    ! [B_168,A_169,B_170] :
      ( ~ m2_orders_2(B_168,A_169,B_170)
      | ~ m2_orders_2(k1_xboole_0,A_169,B_170)
      | ~ m1_orders_1(B_170,k1_orders_1(u1_struct_0(A_169)))
      | ~ l1_orders_2(A_169)
      | ~ v5_orders_2(A_169)
      | ~ v4_orders_2(A_169)
      | ~ v3_orders_2(A_169)
      | v2_struct_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_127,c_392])).

tff(c_407,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_2','#skF_3')
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_405])).

tff(c_410,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_407])).

tff(c_411,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_410])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_418,c_411])).

tff(c_451,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_455,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_451,c_6])).

tff(c_473,plain,(
    ! [B_182,A_183] :
      ( B_182 = A_183
      | ~ r1_tarski(B_182,A_183)
      | ~ r1_tarski(A_183,B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_482,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_455,c_473])).

tff(c_507,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_482])).

tff(c_637,plain,(
    ! [C_219,A_220,B_221] :
      ( m1_subset_1(C_219,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ m2_orders_2(C_219,A_220,B_221)
      | ~ m1_orders_1(B_221,k1_orders_1(u1_struct_0(A_220)))
      | ~ l1_orders_2(A_220)
      | ~ v5_orders_2(A_220)
      | ~ v4_orders_2(A_220)
      | ~ v3_orders_2(A_220)
      | v2_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_639,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_637])).

tff(c_644,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_639])).

tff(c_645,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_644])).

tff(c_18,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_450,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_688,plain,(
    ! [C_235,A_236,D_237,B_238] :
      ( m1_orders_2(C_235,A_236,D_237)
      | m1_orders_2(D_237,A_236,C_235)
      | D_237 = C_235
      | ~ m2_orders_2(D_237,A_236,B_238)
      | ~ m2_orders_2(C_235,A_236,B_238)
      | ~ m1_orders_1(B_238,k1_orders_1(u1_struct_0(A_236)))
      | ~ l1_orders_2(A_236)
      | ~ v5_orders_2(A_236)
      | ~ v4_orders_2(A_236)
      | ~ v3_orders_2(A_236)
      | v2_struct_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_690,plain,(
    ! [C_235] :
      ( m1_orders_2(C_235,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_235)
      | C_235 = '#skF_4'
      | ~ m2_orders_2(C_235,'#skF_2','#skF_3')
      | ~ m1_orders_1('#skF_3',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_688])).

tff(c_695,plain,(
    ! [C_235] :
      ( m1_orders_2(C_235,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_235)
      | C_235 = '#skF_4'
      | ~ m2_orders_2(C_235,'#skF_2','#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_690])).

tff(c_701,plain,(
    ! [C_239] :
      ( m1_orders_2(C_239,'#skF_2','#skF_4')
      | m1_orders_2('#skF_4','#skF_2',C_239)
      | C_239 = '#skF_4'
      | ~ m2_orders_2(C_239,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_695])).

tff(c_707,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | m1_orders_2('#skF_4','#skF_2','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_701])).

tff(c_712,plain,
    ( m1_orders_2('#skF_5','#skF_2','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_450,c_707])).

tff(c_713,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_712])).

tff(c_716,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_507])).

tff(c_725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_716])).

tff(c_726,plain,(
    m1_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_712])).

tff(c_32,plain,(
    ! [C_29,B_27,A_23] :
      ( r1_tarski(C_29,B_27)
      | ~ m1_orders_2(C_29,A_23,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_733,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_726,c_32])).

tff(c_744,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_645,c_733])).

tff(c_746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_507,c_744])).

tff(c_747,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_482])).

tff(c_755,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_451])).

tff(c_759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.55  
% 3.36/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.55  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.36/1.55  
% 3.36/1.55  %Foreground sorts:
% 3.36/1.55  
% 3.36/1.55  
% 3.36/1.55  %Background operators:
% 3.36/1.55  
% 3.36/1.55  
% 3.36/1.55  %Foreground operators:
% 3.36/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.36/1.55  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.36/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.55  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.36/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.55  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.36/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.36/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.55  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.36/1.55  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.36/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.55  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.36/1.55  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.36/1.55  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.36/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.55  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.36/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.55  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.36/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.36/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.36/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.55  
% 3.36/1.57  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.36/1.57  tff(f_220, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 3.36/1.57  tff(f_100, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.36/1.57  tff(f_119, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 3.36/1.57  tff(f_144, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 3.36/1.57  tff(f_60, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.36/1.57  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.36/1.57  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.36/1.57  tff(f_62, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.36/1.57  tff(f_167, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 3.36/1.57  tff(f_195, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 3.36/1.57  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.57  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.36/1.57  tff(c_44, plain, (m2_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.36/1.57  tff(c_54, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.36/1.57  tff(c_52, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.36/1.57  tff(c_50, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.36/1.57  tff(c_48, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.36/1.57  tff(c_46, plain, (m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.36/1.57  tff(c_364, plain, (![C_155, A_156, B_157]: (m1_subset_1(C_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~m2_orders_2(C_155, A_156, B_157) | ~m1_orders_1(B_157, k1_orders_1(u1_struct_0(A_156))) | ~l1_orders_2(A_156) | ~v5_orders_2(A_156) | ~v4_orders_2(A_156) | ~v3_orders_2(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.36/1.57  tff(c_366, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_364])).
% 3.36/1.57  tff(c_369, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_366])).
% 3.36/1.57  tff(c_370, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_369])).
% 3.36/1.57  tff(c_105, plain, (![A_90, B_91]: (r2_xboole_0(A_90, B_91) | B_91=A_90 | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.57  tff(c_58, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.36/1.57  tff(c_72, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_58])).
% 3.36/1.57  tff(c_116, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_105, c_72])).
% 3.36/1.57  tff(c_137, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_116])).
% 3.36/1.57  tff(c_64, plain, (r2_xboole_0('#skF_4', '#skF_5') | m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.36/1.57  tff(c_73, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_64])).
% 3.36/1.57  tff(c_168, plain, (![C_106, B_107, A_108]: (r1_tarski(C_106, B_107) | ~m1_orders_2(C_106, A_108, B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_orders_2(A_108) | ~v5_orders_2(A_108) | ~v4_orders_2(A_108) | ~v3_orders_2(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.36/1.57  tff(c_170, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_73, c_168])).
% 3.36/1.57  tff(c_173, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_170])).
% 3.36/1.57  tff(c_174, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_137, c_173])).
% 3.36/1.57  tff(c_42, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.36/1.57  tff(c_227, plain, (![C_119, A_120, B_121]: (m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~m2_orders_2(C_119, A_120, B_121) | ~m1_orders_1(B_121, k1_orders_1(u1_struct_0(A_120))) | ~l1_orders_2(A_120) | ~v5_orders_2(A_120) | ~v4_orders_2(A_120) | ~v3_orders_2(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.36/1.57  tff(c_231, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_227])).
% 3.36/1.57  tff(c_238, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_231])).
% 3.36/1.57  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_174, c_238])).
% 3.36/1.57  tff(c_241, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_116])).
% 3.36/1.57  tff(c_243, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_73])).
% 3.36/1.57  tff(c_412, plain, (![C_171, A_172, B_173]: (~m1_orders_2(C_171, A_172, B_173) | ~m1_orders_2(B_173, A_172, C_171) | k1_xboole_0=B_173 | ~m1_subset_1(C_171, k1_zfmisc_1(u1_struct_0(A_172))) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_orders_2(A_172) | ~v5_orders_2(A_172) | ~v4_orders_2(A_172) | ~v3_orders_2(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.36/1.57  tff(c_414, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_243, c_412])).
% 3.36/1.57  tff(c_417, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_370, c_243, c_414])).
% 3.36/1.57  tff(c_418, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_417])).
% 3.36/1.57  tff(c_22, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.36/1.57  tff(c_20, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.36/1.57  tff(c_74, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.36/1.57  tff(c_87, plain, (![A_89]: (k1_xboole_0=A_89 | ~r1_tarski(A_89, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_74])).
% 3.36/1.57  tff(c_122, plain, (![B_92]: (k4_xboole_0(k1_xboole_0, B_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_87])).
% 3.36/1.57  tff(c_24, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.36/1.57  tff(c_127, plain, (![B_92]: (r1_xboole_0(k1_xboole_0, B_92))), inference(superposition, [status(thm), theory('equality')], [c_122, c_24])).
% 3.36/1.57  tff(c_392, plain, (![C_164, D_165, A_166, B_167]: (~r1_xboole_0(C_164, D_165) | ~m2_orders_2(D_165, A_166, B_167) | ~m2_orders_2(C_164, A_166, B_167) | ~m1_orders_1(B_167, k1_orders_1(u1_struct_0(A_166))) | ~l1_orders_2(A_166) | ~v5_orders_2(A_166) | ~v4_orders_2(A_166) | ~v3_orders_2(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.36/1.57  tff(c_405, plain, (![B_168, A_169, B_170]: (~m2_orders_2(B_168, A_169, B_170) | ~m2_orders_2(k1_xboole_0, A_169, B_170) | ~m1_orders_1(B_170, k1_orders_1(u1_struct_0(A_169))) | ~l1_orders_2(A_169) | ~v5_orders_2(A_169) | ~v4_orders_2(A_169) | ~v3_orders_2(A_169) | v2_struct_0(A_169))), inference(resolution, [status(thm)], [c_127, c_392])).
% 3.36/1.57  tff(c_407, plain, (~m2_orders_2(k1_xboole_0, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_405])).
% 3.36/1.57  tff(c_410, plain, (~m2_orders_2(k1_xboole_0, '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_407])).
% 3.36/1.57  tff(c_411, plain, (~m2_orders_2(k1_xboole_0, '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_410])).
% 3.36/1.57  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_418, c_411])).
% 3.36/1.57  tff(c_451, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 3.36/1.57  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.36/1.57  tff(c_455, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_451, c_6])).
% 3.36/1.57  tff(c_473, plain, (![B_182, A_183]: (B_182=A_183 | ~r1_tarski(B_182, A_183) | ~r1_tarski(A_183, B_182))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.36/1.57  tff(c_482, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_455, c_473])).
% 3.36/1.57  tff(c_507, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_482])).
% 3.36/1.57  tff(c_637, plain, (![C_219, A_220, B_221]: (m1_subset_1(C_219, k1_zfmisc_1(u1_struct_0(A_220))) | ~m2_orders_2(C_219, A_220, B_221) | ~m1_orders_1(B_221, k1_orders_1(u1_struct_0(A_220))) | ~l1_orders_2(A_220) | ~v5_orders_2(A_220) | ~v4_orders_2(A_220) | ~v3_orders_2(A_220) | v2_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.36/1.57  tff(c_639, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_637])).
% 3.36/1.57  tff(c_644, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_639])).
% 3.36/1.57  tff(c_645, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_644])).
% 3.36/1.57  tff(c_18, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.36/1.57  tff(c_450, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 3.36/1.57  tff(c_688, plain, (![C_235, A_236, D_237, B_238]: (m1_orders_2(C_235, A_236, D_237) | m1_orders_2(D_237, A_236, C_235) | D_237=C_235 | ~m2_orders_2(D_237, A_236, B_238) | ~m2_orders_2(C_235, A_236, B_238) | ~m1_orders_1(B_238, k1_orders_1(u1_struct_0(A_236))) | ~l1_orders_2(A_236) | ~v5_orders_2(A_236) | ~v4_orders_2(A_236) | ~v3_orders_2(A_236) | v2_struct_0(A_236))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.36/1.57  tff(c_690, plain, (![C_235]: (m1_orders_2(C_235, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_235) | C_235='#skF_4' | ~m2_orders_2(C_235, '#skF_2', '#skF_3') | ~m1_orders_1('#skF_3', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_688])).
% 3.36/1.57  tff(c_695, plain, (![C_235]: (m1_orders_2(C_235, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_235) | C_235='#skF_4' | ~m2_orders_2(C_235, '#skF_2', '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_690])).
% 3.36/1.57  tff(c_701, plain, (![C_239]: (m1_orders_2(C_239, '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', C_239) | C_239='#skF_4' | ~m2_orders_2(C_239, '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_695])).
% 3.36/1.57  tff(c_707, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | m1_orders_2('#skF_4', '#skF_2', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_42, c_701])).
% 3.36/1.57  tff(c_712, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4') | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_450, c_707])).
% 3.36/1.57  tff(c_713, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_712])).
% 3.36/1.57  tff(c_716, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_713, c_507])).
% 3.36/1.57  tff(c_725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_716])).
% 3.36/1.57  tff(c_726, plain, (m1_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_712])).
% 3.36/1.57  tff(c_32, plain, (![C_29, B_27, A_23]: (r1_tarski(C_29, B_27) | ~m1_orders_2(C_29, A_23, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23) | ~v4_orders_2(A_23) | ~v3_orders_2(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.36/1.57  tff(c_733, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_726, c_32])).
% 3.36/1.57  tff(c_744, plain, (r1_tarski('#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_645, c_733])).
% 3.36/1.57  tff(c_746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_507, c_744])).
% 3.36/1.57  tff(c_747, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_482])).
% 3.36/1.57  tff(c_755, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_747, c_451])).
% 3.36/1.57  tff(c_759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_755])).
% 3.36/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.57  
% 3.36/1.57  Inference rules
% 3.36/1.57  ----------------------
% 3.36/1.57  #Ref     : 0
% 3.36/1.57  #Sup     : 128
% 3.36/1.57  #Fact    : 0
% 3.36/1.57  #Define  : 0
% 3.36/1.57  #Split   : 4
% 3.36/1.57  #Chain   : 0
% 3.36/1.57  #Close   : 0
% 3.36/1.57  
% 3.36/1.57  Ordering : KBO
% 3.36/1.57  
% 3.36/1.57  Simplification rules
% 3.36/1.57  ----------------------
% 3.36/1.57  #Subsume      : 20
% 3.36/1.57  #Demod        : 185
% 3.36/1.57  #Tautology    : 56
% 3.36/1.57  #SimpNegUnit  : 26
% 3.36/1.57  #BackRed      : 23
% 3.36/1.57  
% 3.36/1.57  #Partial instantiations: 0
% 3.36/1.57  #Strategies tried      : 1
% 3.36/1.57  
% 3.36/1.57  Timing (in seconds)
% 3.36/1.57  ----------------------
% 3.36/1.58  Preprocessing        : 0.34
% 3.36/1.58  Parsing              : 0.19
% 3.36/1.58  CNF conversion       : 0.03
% 3.36/1.58  Main loop            : 0.38
% 3.36/1.58  Inferencing          : 0.15
% 3.36/1.58  Reduction            : 0.12
% 3.36/1.58  Demodulation         : 0.09
% 3.36/1.58  BG Simplification    : 0.02
% 3.36/1.58  Subsumption          : 0.07
% 3.36/1.58  Abstraction          : 0.02
% 3.36/1.58  MUC search           : 0.00
% 3.36/1.58  Cooper               : 0.00
% 3.36/1.58  Total                : 0.76
% 3.36/1.58  Index Insertion      : 0.00
% 3.36/1.58  Index Deletion       : 0.00
% 3.36/1.58  Index Matching       : 0.00
% 3.36/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
