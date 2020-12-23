%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:59 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 329 expanded)
%              Number of leaves         :   37 ( 136 expanded)
%              Depth                    :   13
%              Number of atoms          :  326 (1403 expanded)
%              Number of equality atoms :   35 (  65 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_207,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_154,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_182,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_52,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_50,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_48,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_46,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_40,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_44,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_442,plain,(
    ! [C_121,A_122,B_123] :
      ( m1_subset_1(C_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m2_orders_2(C_121,A_122,B_123)
      | ~ m1_orders_1(B_123,k1_orders_1(u1_struct_0(A_122)))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_444,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_442])).

tff(c_447,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_444])).

tff(c_448,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_447])).

tff(c_205,plain,(
    ! [A_88,B_89] :
      ( r2_xboole_0(A_88,B_89)
      | B_89 = A_88
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_92,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_216,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_205,c_92])).

tff(c_222,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_62,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_120,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_62])).

tff(c_227,plain,(
    ! [C_90,B_91,A_92] :
      ( r1_tarski(C_90,B_91)
      | ~ m1_orders_2(C_90,A_92,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_orders_2(A_92)
      | ~ v5_orders_2(A_92)
      | ~ v4_orders_2(A_92)
      | ~ v3_orders_2(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_229,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_227])).

tff(c_232,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_229])).

tff(c_233,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_222,c_232])).

tff(c_325,plain,(
    ! [C_104,A_105,B_106] :
      ( m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m2_orders_2(C_104,A_105,B_106)
      | ~ m1_orders_1(B_106,k1_orders_1(u1_struct_0(A_105)))
      | ~ l1_orders_2(A_105)
      | ~ v5_orders_2(A_105)
      | ~ v4_orders_2(A_105)
      | ~ v3_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_329,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_325])).

tff(c_336,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_329])).

tff(c_338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_233,c_336])).

tff(c_339,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_341,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_120])).

tff(c_461,plain,(
    ! [C_130,A_131,B_132] :
      ( ~ m1_orders_2(C_130,A_131,B_132)
      | ~ m1_orders_2(B_132,A_131,C_130)
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_orders_2(A_131)
      | ~ v5_orders_2(A_131)
      | ~ v4_orders_2(A_131)
      | ~ v3_orders_2(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_463,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_341,c_461])).

tff(c_466,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_448,c_341,c_463])).

tff(c_467,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_466])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = k1_xboole_0
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_102,plain,(
    ! [B_79] : k4_xboole_0(B_79,B_79) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_93])).

tff(c_18,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    ! [B_79] : r1_tarski(k1_xboole_0,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_18])).

tff(c_475,plain,(
    ! [B_79] : r1_tarski('#skF_4',B_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_110])).

tff(c_456,plain,(
    ! [B_127,A_128,C_129] :
      ( r2_hidden(k1_funct_1(B_127,u1_struct_0(A_128)),C_129)
      | ~ m2_orders_2(C_129,A_128,B_127)
      | ~ m1_orders_1(B_127,k1_orders_1(u1_struct_0(A_128)))
      | ~ l1_orders_2(A_128)
      | ~ v5_orders_2(A_128)
      | ~ v4_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_711,plain,(
    ! [C_159,B_160,A_161] :
      ( ~ r1_tarski(C_159,k1_funct_1(B_160,u1_struct_0(A_161)))
      | ~ m2_orders_2(C_159,A_161,B_160)
      | ~ m1_orders_1(B_160,k1_orders_1(u1_struct_0(A_161)))
      | ~ l1_orders_2(A_161)
      | ~ v5_orders_2(A_161)
      | ~ v4_orders_2(A_161)
      | ~ v3_orders_2(A_161)
      | v2_struct_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_456,c_22])).

tff(c_733,plain,(
    ! [A_164,B_165] :
      ( ~ m2_orders_2('#skF_4',A_164,B_165)
      | ~ m1_orders_1(B_165,k1_orders_1(u1_struct_0(A_164)))
      | ~ l1_orders_2(A_164)
      | ~ v5_orders_2(A_164)
      | ~ v4_orders_2(A_164)
      | ~ v3_orders_2(A_164)
      | v2_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_475,c_711])).

tff(c_736,plain,
    ( ~ m2_orders_2('#skF_4','#skF_1','#skF_2')
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_733])).

tff(c_739,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_40,c_736])).

tff(c_741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_739])).

tff(c_743,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_747,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_743,c_6])).

tff(c_874,plain,(
    ! [B_177,A_178] :
      ( B_177 = A_178
      | ~ r1_tarski(B_177,A_178)
      | ~ r1_tarski(A_178,B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_887,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_747,c_874])).

tff(c_894,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_887])).

tff(c_42,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_989,plain,(
    ! [C_191,A_192,B_193] :
      ( m1_subset_1(C_191,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ m2_orders_2(C_191,A_192,B_193)
      | ~ m1_orders_1(B_193,k1_orders_1(u1_struct_0(A_192)))
      | ~ l1_orders_2(A_192)
      | ~ v5_orders_2(A_192)
      | ~ v4_orders_2(A_192)
      | ~ v3_orders_2(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_991,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_989])).

tff(c_996,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_991])).

tff(c_997,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_996])).

tff(c_748,plain,(
    ! [A_166,B_167] :
      ( k4_xboole_0(A_166,B_167) = k1_xboole_0
      | ~ r1_tarski(A_166,B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_760,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_748])).

tff(c_742,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1087,plain,(
    ! [C_224,A_225,D_226,B_227] :
      ( m1_orders_2(C_224,A_225,D_226)
      | m1_orders_2(D_226,A_225,C_224)
      | D_226 = C_224
      | ~ m2_orders_2(D_226,A_225,B_227)
      | ~ m2_orders_2(C_224,A_225,B_227)
      | ~ m1_orders_1(B_227,k1_orders_1(u1_struct_0(A_225)))
      | ~ l1_orders_2(A_225)
      | ~ v5_orders_2(A_225)
      | ~ v4_orders_2(A_225)
      | ~ v3_orders_2(A_225)
      | v2_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1089,plain,(
    ! [C_224] :
      ( m1_orders_2(C_224,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_224)
      | C_224 = '#skF_3'
      | ~ m2_orders_2(C_224,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_1087])).

tff(c_1094,plain,(
    ! [C_224] :
      ( m1_orders_2(C_224,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_224)
      | C_224 = '#skF_3'
      | ~ m2_orders_2(C_224,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_1089])).

tff(c_1100,plain,(
    ! [C_228] :
      ( m1_orders_2(C_228,'#skF_1','#skF_3')
      | m1_orders_2('#skF_3','#skF_1',C_228)
      | C_228 = '#skF_3'
      | ~ m2_orders_2(C_228,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1094])).

tff(c_1106,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | m1_orders_2('#skF_3','#skF_1','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_1100])).

tff(c_1111,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_742,c_1106])).

tff(c_1124,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1111])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_898,plain,(
    k4_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_894])).

tff(c_1128,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_898])).

tff(c_1139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_1128])).

tff(c_1141,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1111])).

tff(c_1091,plain,(
    ! [C_224] :
      ( m1_orders_2(C_224,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_224)
      | C_224 = '#skF_4'
      | ~ m2_orders_2(C_224,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_1087])).

tff(c_1098,plain,(
    ! [C_224] :
      ( m1_orders_2(C_224,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_224)
      | C_224 = '#skF_4'
      | ~ m2_orders_2(C_224,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_1091])).

tff(c_1112,plain,(
    ! [C_229] :
      ( m1_orders_2(C_229,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_229)
      | C_229 = '#skF_4'
      | ~ m2_orders_2(C_229,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1098])).

tff(c_1115,plain,
    ( m1_orders_2('#skF_3','#skF_1','#skF_4')
    | m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_1112])).

tff(c_1121,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_742,c_1115])).

tff(c_1142,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1141,c_1121])).

tff(c_30,plain,(
    ! [C_26,B_24,A_20] :
      ( r1_tarski(C_26,B_24)
      | ~ m1_orders_2(C_26,A_20,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_orders_2(A_20)
      | ~ v5_orders_2(A_20)
      | ~ v4_orders_2(A_20)
      | ~ v3_orders_2(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1150,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1142,c_30])).

tff(c_1165,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_997,c_1150])).

tff(c_1167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_894,c_1165])).

tff(c_1168,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_887])).

tff(c_1173,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1168,c_743])).

tff(c_1178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_1173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.56  
% 3.39/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.57  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.39/1.57  
% 3.39/1.57  %Foreground sorts:
% 3.39/1.57  
% 3.39/1.57  
% 3.39/1.57  %Background operators:
% 3.39/1.57  
% 3.39/1.57  
% 3.39/1.57  %Foreground operators:
% 3.39/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.39/1.57  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.39/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.39/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.57  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.39/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.57  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.39/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.57  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.39/1.57  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.39/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.57  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.39/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.39/1.57  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.39/1.57  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.39/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.57  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.39/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.57  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.39/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.39/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.57  
% 3.39/1.59  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.39/1.59  tff(f_207, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 3.39/1.59  tff(f_91, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.39/1.59  tff(f_110, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 3.39/1.59  tff(f_135, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 3.39/1.59  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.39/1.59  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.39/1.59  tff(f_44, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.39/1.59  tff(f_154, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 3.39/1.59  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.39/1.59  tff(f_182, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 3.39/1.59  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.59  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.39/1.59  tff(c_52, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.39/1.59  tff(c_50, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.39/1.59  tff(c_48, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.39/1.59  tff(c_46, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.39/1.59  tff(c_40, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.39/1.59  tff(c_44, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.39/1.59  tff(c_442, plain, (![C_121, A_122, B_123]: (m1_subset_1(C_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~m2_orders_2(C_121, A_122, B_123) | ~m1_orders_1(B_123, k1_orders_1(u1_struct_0(A_122))) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.39/1.59  tff(c_444, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_442])).
% 3.39/1.59  tff(c_447, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_444])).
% 3.39/1.59  tff(c_448, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_447])).
% 3.39/1.59  tff(c_205, plain, (![A_88, B_89]: (r2_xboole_0(A_88, B_89) | B_89=A_88 | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.59  tff(c_56, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.39/1.59  tff(c_92, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 3.39/1.59  tff(c_216, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_205, c_92])).
% 3.39/1.59  tff(c_222, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_216])).
% 3.39/1.59  tff(c_62, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.39/1.59  tff(c_120, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_92, c_62])).
% 3.39/1.59  tff(c_227, plain, (![C_90, B_91, A_92]: (r1_tarski(C_90, B_91) | ~m1_orders_2(C_90, A_92, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_orders_2(A_92) | ~v5_orders_2(A_92) | ~v4_orders_2(A_92) | ~v3_orders_2(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.39/1.59  tff(c_229, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_120, c_227])).
% 3.39/1.59  tff(c_232, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_229])).
% 3.39/1.59  tff(c_233, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_222, c_232])).
% 3.39/1.59  tff(c_325, plain, (![C_104, A_105, B_106]: (m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~m2_orders_2(C_104, A_105, B_106) | ~m1_orders_1(B_106, k1_orders_1(u1_struct_0(A_105))) | ~l1_orders_2(A_105) | ~v5_orders_2(A_105) | ~v4_orders_2(A_105) | ~v3_orders_2(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.39/1.59  tff(c_329, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_325])).
% 3.39/1.59  tff(c_336, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_329])).
% 3.39/1.59  tff(c_338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_233, c_336])).
% 3.39/1.59  tff(c_339, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_216])).
% 3.39/1.59  tff(c_341, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_120])).
% 3.39/1.59  tff(c_461, plain, (![C_130, A_131, B_132]: (~m1_orders_2(C_130, A_131, B_132) | ~m1_orders_2(B_132, A_131, C_130) | k1_xboole_0=B_132 | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_orders_2(A_131) | ~v5_orders_2(A_131) | ~v4_orders_2(A_131) | ~v3_orders_2(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.39/1.59  tff(c_463, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_341, c_461])).
% 3.39/1.59  tff(c_466, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_448, c_341, c_463])).
% 3.39/1.59  tff(c_467, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_466])).
% 3.39/1.59  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.59  tff(c_93, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=k1_xboole_0 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.59  tff(c_102, plain, (![B_79]: (k4_xboole_0(B_79, B_79)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_93])).
% 3.39/1.59  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.39/1.59  tff(c_110, plain, (![B_79]: (r1_tarski(k1_xboole_0, B_79))), inference(superposition, [status(thm), theory('equality')], [c_102, c_18])).
% 3.39/1.59  tff(c_475, plain, (![B_79]: (r1_tarski('#skF_4', B_79))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_110])).
% 3.39/1.59  tff(c_456, plain, (![B_127, A_128, C_129]: (r2_hidden(k1_funct_1(B_127, u1_struct_0(A_128)), C_129) | ~m2_orders_2(C_129, A_128, B_127) | ~m1_orders_1(B_127, k1_orders_1(u1_struct_0(A_128))) | ~l1_orders_2(A_128) | ~v5_orders_2(A_128) | ~v4_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.39/1.59  tff(c_22, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.39/1.59  tff(c_711, plain, (![C_159, B_160, A_161]: (~r1_tarski(C_159, k1_funct_1(B_160, u1_struct_0(A_161))) | ~m2_orders_2(C_159, A_161, B_160) | ~m1_orders_1(B_160, k1_orders_1(u1_struct_0(A_161))) | ~l1_orders_2(A_161) | ~v5_orders_2(A_161) | ~v4_orders_2(A_161) | ~v3_orders_2(A_161) | v2_struct_0(A_161))), inference(resolution, [status(thm)], [c_456, c_22])).
% 3.39/1.59  tff(c_733, plain, (![A_164, B_165]: (~m2_orders_2('#skF_4', A_164, B_165) | ~m1_orders_1(B_165, k1_orders_1(u1_struct_0(A_164))) | ~l1_orders_2(A_164) | ~v5_orders_2(A_164) | ~v4_orders_2(A_164) | ~v3_orders_2(A_164) | v2_struct_0(A_164))), inference(resolution, [status(thm)], [c_475, c_711])).
% 3.39/1.59  tff(c_736, plain, (~m2_orders_2('#skF_4', '#skF_1', '#skF_2') | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_733])).
% 3.39/1.59  tff(c_739, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_40, c_736])).
% 3.39/1.59  tff(c_741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_739])).
% 3.39/1.59  tff(c_743, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 3.39/1.59  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.59  tff(c_747, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_743, c_6])).
% 3.39/1.59  tff(c_874, plain, (![B_177, A_178]: (B_177=A_178 | ~r1_tarski(B_177, A_178) | ~r1_tarski(A_178, B_177))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.59  tff(c_887, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_747, c_874])).
% 3.39/1.59  tff(c_894, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_887])).
% 3.39/1.59  tff(c_42, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.39/1.59  tff(c_989, plain, (![C_191, A_192, B_193]: (m1_subset_1(C_191, k1_zfmisc_1(u1_struct_0(A_192))) | ~m2_orders_2(C_191, A_192, B_193) | ~m1_orders_1(B_193, k1_orders_1(u1_struct_0(A_192))) | ~l1_orders_2(A_192) | ~v5_orders_2(A_192) | ~v4_orders_2(A_192) | ~v3_orders_2(A_192) | v2_struct_0(A_192))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.39/1.59  tff(c_991, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_989])).
% 3.39/1.59  tff(c_996, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_991])).
% 3.39/1.59  tff(c_997, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_996])).
% 3.39/1.59  tff(c_748, plain, (![A_166, B_167]: (k4_xboole_0(A_166, B_167)=k1_xboole_0 | ~r1_tarski(A_166, B_167))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.59  tff(c_760, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_748])).
% 3.39/1.59  tff(c_742, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 3.39/1.59  tff(c_1087, plain, (![C_224, A_225, D_226, B_227]: (m1_orders_2(C_224, A_225, D_226) | m1_orders_2(D_226, A_225, C_224) | D_226=C_224 | ~m2_orders_2(D_226, A_225, B_227) | ~m2_orders_2(C_224, A_225, B_227) | ~m1_orders_1(B_227, k1_orders_1(u1_struct_0(A_225))) | ~l1_orders_2(A_225) | ~v5_orders_2(A_225) | ~v4_orders_2(A_225) | ~v3_orders_2(A_225) | v2_struct_0(A_225))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.39/1.59  tff(c_1089, plain, (![C_224]: (m1_orders_2(C_224, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_224) | C_224='#skF_3' | ~m2_orders_2(C_224, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_1087])).
% 3.39/1.59  tff(c_1094, plain, (![C_224]: (m1_orders_2(C_224, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_224) | C_224='#skF_3' | ~m2_orders_2(C_224, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_1089])).
% 3.39/1.59  tff(c_1100, plain, (![C_228]: (m1_orders_2(C_228, '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', C_228) | C_228='#skF_3' | ~m2_orders_2(C_228, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1094])).
% 3.39/1.59  tff(c_1106, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | m1_orders_2('#skF_3', '#skF_1', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_40, c_1100])).
% 3.39/1.59  tff(c_1111, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_742, c_1106])).
% 3.39/1.59  tff(c_1124, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_1111])).
% 3.39/1.59  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.59  tff(c_898, plain, (k4_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_894])).
% 3.39/1.59  tff(c_1128, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_898])).
% 3.39/1.59  tff(c_1139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_760, c_1128])).
% 3.39/1.59  tff(c_1141, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_1111])).
% 3.39/1.59  tff(c_1091, plain, (![C_224]: (m1_orders_2(C_224, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_224) | C_224='#skF_4' | ~m2_orders_2(C_224, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_1087])).
% 3.39/1.59  tff(c_1098, plain, (![C_224]: (m1_orders_2(C_224, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_224) | C_224='#skF_4' | ~m2_orders_2(C_224, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_1091])).
% 3.39/1.59  tff(c_1112, plain, (![C_229]: (m1_orders_2(C_229, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_229) | C_229='#skF_4' | ~m2_orders_2(C_229, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1098])).
% 3.39/1.59  tff(c_1115, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_42, c_1112])).
% 3.39/1.59  tff(c_1121, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_742, c_1115])).
% 3.39/1.59  tff(c_1142, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1141, c_1121])).
% 3.39/1.59  tff(c_30, plain, (![C_26, B_24, A_20]: (r1_tarski(C_26, B_24) | ~m1_orders_2(C_26, A_20, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20) | ~v4_orders_2(A_20) | ~v3_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.39/1.59  tff(c_1150, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1142, c_30])).
% 3.39/1.59  tff(c_1165, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_997, c_1150])).
% 3.39/1.59  tff(c_1167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_894, c_1165])).
% 3.39/1.59  tff(c_1168, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_887])).
% 3.39/1.59  tff(c_1173, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1168, c_743])).
% 3.39/1.59  tff(c_1178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_1173])).
% 3.39/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.59  
% 3.39/1.59  Inference rules
% 3.39/1.59  ----------------------
% 3.39/1.59  #Ref     : 0
% 3.39/1.59  #Sup     : 214
% 3.39/1.59  #Fact    : 0
% 3.39/1.59  #Define  : 0
% 3.39/1.59  #Split   : 4
% 3.39/1.59  #Chain   : 0
% 3.39/1.59  #Close   : 0
% 3.39/1.59  
% 3.39/1.59  Ordering : KBO
% 3.39/1.59  
% 3.39/1.59  Simplification rules
% 3.39/1.59  ----------------------
% 3.39/1.59  #Subsume      : 50
% 3.39/1.59  #Demod        : 256
% 3.39/1.59  #Tautology    : 118
% 3.39/1.59  #SimpNegUnit  : 31
% 3.39/1.59  #BackRed      : 30
% 3.39/1.59  
% 3.39/1.59  #Partial instantiations: 0
% 3.39/1.59  #Strategies tried      : 1
% 3.39/1.59  
% 3.39/1.59  Timing (in seconds)
% 3.39/1.59  ----------------------
% 3.39/1.59  Preprocessing        : 0.39
% 3.39/1.59  Parsing              : 0.22
% 3.39/1.59  CNF conversion       : 0.03
% 3.39/1.59  Main loop            : 0.42
% 3.39/1.59  Inferencing          : 0.16
% 3.39/1.59  Reduction            : 0.13
% 3.39/1.59  Demodulation         : 0.10
% 3.39/1.59  BG Simplification    : 0.02
% 3.39/1.59  Subsumption          : 0.08
% 3.39/1.59  Abstraction          : 0.02
% 3.39/1.59  MUC search           : 0.00
% 3.39/1.59  Cooper               : 0.00
% 3.39/1.59  Total                : 0.86
% 3.39/1.59  Index Insertion      : 0.00
% 3.39/1.59  Index Deletion       : 0.00
% 3.39/1.59  Index Matching       : 0.00
% 3.39/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
