%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:21 EST 2020

% Result     : Theorem 5.16s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 363 expanded)
%              Number of leaves         :   53 ( 143 expanded)
%              Depth                    :   13
%              Number of atoms          :  203 (1029 expanded)
%              Number of equality atoms :   35 ( 148 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_157,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_101,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_84,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_10] : r1_tarski('#skF_6',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16])).

tff(c_76,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_74,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_64,plain,(
    ! [A_66] :
      ( v4_pre_topc(k2_struct_0(A_66),A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_125,plain,(
    ! [A_91] :
      ( v1_xboole_0(A_91)
      | r2_hidden('#skF_1'(A_91),A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [B_62,A_61] :
      ( ~ r1_tarski(B_62,A_61)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_139,plain,(
    ! [A_94] :
      ( ~ r1_tarski(A_94,'#skF_1'(A_94))
      | v1_xboole_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_125,c_56])).

tff(c_144,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_91,c_139])).

tff(c_60,plain,(
    ! [A_64] :
      ( l1_struct_0(A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_119,plain,(
    ! [A_88] :
      ( u1_struct_0(A_88) = k2_struct_0(A_88)
      | ~ l1_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_145,plain,(
    ! [A_95] :
      ( u1_struct_0(A_95) = k2_struct_0(A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_60,c_119])).

tff(c_149,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_145])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_157,plain,(
    m1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_72])).

tff(c_48,plain,(
    ! [C_53,A_47,B_51] :
      ( r2_hidden(C_53,k3_subset_1(A_47,B_51))
      | r2_hidden(C_53,B_51)
      | ~ m1_subset_1(C_53,A_47)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_47))
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2542,plain,(
    ! [C_307,A_308,B_309] :
      ( r2_hidden(C_307,k3_subset_1(A_308,B_309))
      | r2_hidden(C_307,B_309)
      | ~ m1_subset_1(C_307,A_308)
      | ~ m1_subset_1(B_309,k1_zfmisc_1(A_308))
      | A_308 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2928,plain,(
    ! [A_326,B_327,C_328] :
      ( ~ v1_xboole_0(k3_subset_1(A_326,B_327))
      | r2_hidden(C_328,B_327)
      | ~ m1_subset_1(C_328,A_326)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(A_326))
      | A_326 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_2542,c_2])).

tff(c_2954,plain,(
    ! [B_327] :
      ( ~ v1_xboole_0(k3_subset_1(k2_struct_0('#skF_4'),B_327))
      | r2_hidden('#skF_5',B_327)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | k2_struct_0('#skF_4') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_157,c_2928])).

tff(c_2979,plain,(
    k2_struct_0('#skF_4') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2954])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_188,plain,(
    ! [A_104] :
      ( ~ v1_xboole_0(u1_struct_0(A_104))
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_191,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_188])).

tff(c_192,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_191])).

tff(c_205,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_208,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_205])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_208])).

tff(c_213,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_2991,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2979,c_213])).

tff(c_2998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_2991])).

tff(c_3000,plain,(
    k2_struct_0('#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2954])).

tff(c_46,plain,(
    ! [A_46] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_88,plain,(
    ! [A_46] : m1_subset_1('#skF_6',k1_zfmisc_1(A_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_46])).

tff(c_18,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_90,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_6') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_18])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92,plain,(
    ! [A_9] : k3_xboole_0(A_9,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_14])).

tff(c_268,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k3_xboole_0(A_116,B_117)) = k4_xboole_0(A_116,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_277,plain,(
    ! [A_9] : k5_xboole_0(A_9,'#skF_6') = k4_xboole_0(A_9,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_268])).

tff(c_280,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_6') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_277])).

tff(c_1746,plain,(
    ! [A_230,B_231] :
      ( k4_xboole_0(A_230,B_231) = k3_subset_1(A_230,B_231)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(A_230)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1760,plain,(
    ! [A_46] : k4_xboole_0(A_46,'#skF_6') = k3_subset_1(A_46,'#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_1746])).

tff(c_1765,plain,(
    ! [A_46] : k3_subset_1(A_46,'#skF_6') = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_1760])).

tff(c_2567,plain,(
    ! [C_307,A_46] :
      ( r2_hidden(C_307,A_46)
      | r2_hidden(C_307,'#skF_6')
      | ~ m1_subset_1(C_307,A_46)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_46))
      | A_46 = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1765,c_2542])).

tff(c_2593,plain,(
    ! [C_310,A_311] :
      ( r2_hidden(C_310,A_311)
      | r2_hidden(C_310,'#skF_6')
      | ~ m1_subset_1(C_310,A_311)
      | A_311 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2567])).

tff(c_2664,plain,(
    ! [C_310,A_311] :
      ( ~ r1_tarski('#skF_6',C_310)
      | r2_hidden(C_310,A_311)
      | ~ m1_subset_1(C_310,A_311)
      | A_311 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_2593,c_56])).

tff(c_2694,plain,(
    ! [C_310,A_311] :
      ( r2_hidden(C_310,A_311)
      | ~ m1_subset_1(C_310,A_311)
      | A_311 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_2664])).

tff(c_66,plain,(
    ! [A_67] :
      ( v3_pre_topc(k2_struct_0(A_67),A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_170,plain,(
    ! [C_100,A_101] :
      ( r2_hidden(C_100,k1_zfmisc_1(A_101))
      | ~ r1_tarski(C_100,A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(A_56,B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_245,plain,(
    ! [C_113,A_114] :
      ( m1_subset_1(C_113,k1_zfmisc_1(A_114))
      | ~ r1_tarski(C_113,A_114) ) ),
    inference(resolution,[status(thm)],[c_170,c_52])).

tff(c_82,plain,(
    ! [D_79] :
      ( r2_hidden('#skF_5',D_79)
      | ~ r2_hidden(D_79,'#skF_6')
      | ~ m1_subset_1(D_79,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_193,plain,(
    ! [D_79] :
      ( r2_hidden('#skF_5',D_79)
      | ~ r2_hidden(D_79,'#skF_6')
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_82])).

tff(c_1831,plain,(
    ! [C_237] :
      ( r2_hidden('#skF_5',C_237)
      | ~ r2_hidden(C_237,'#skF_6')
      | ~ r1_tarski(C_237,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_245,c_193])).

tff(c_1845,plain,
    ( r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ r2_hidden(k2_struct_0('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_1831])).

tff(c_1848,plain,(
    ~ r2_hidden(k2_struct_0('#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1845])).

tff(c_184,plain,(
    ! [C_100,A_101] :
      ( m1_subset_1(C_100,k1_zfmisc_1(A_101))
      | ~ r1_tarski(C_100,A_101) ) ),
    inference(resolution,[status(thm)],[c_170,c_52])).

tff(c_80,plain,(
    ! [D_79] :
      ( r2_hidden(D_79,'#skF_6')
      | ~ r2_hidden('#skF_5',D_79)
      | ~ v4_pre_topc(D_79,'#skF_4')
      | ~ v3_pre_topc(D_79,'#skF_4')
      | ~ m1_subset_1(D_79,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_448,plain,(
    ! [D_139] :
      ( r2_hidden(D_139,'#skF_6')
      | ~ r2_hidden('#skF_5',D_139)
      | ~ v4_pre_topc(D_139,'#skF_4')
      | ~ v3_pre_topc(D_139,'#skF_4')
      | ~ m1_subset_1(D_139,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_80])).

tff(c_3469,plain,(
    ! [C_352] :
      ( r2_hidden(C_352,'#skF_6')
      | ~ r2_hidden('#skF_5',C_352)
      | ~ v4_pre_topc(C_352,'#skF_4')
      | ~ v3_pre_topc(C_352,'#skF_4')
      | ~ r1_tarski(C_352,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_184,c_448])).

tff(c_3505,plain,
    ( r2_hidden(k2_struct_0('#skF_4'),'#skF_6')
    | ~ r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_3469])).

tff(c_3522,plain,
    ( ~ r2_hidden('#skF_5',k2_struct_0('#skF_4'))
    | ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1848,c_3505])).

tff(c_3527,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3522])).

tff(c_3530,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_3527])).

tff(c_3534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_3530])).

tff(c_3535,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3522])).

tff(c_3537,plain,(
    ~ r2_hidden('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3535])).

tff(c_3540,plain,
    ( ~ m1_subset_1('#skF_5',k2_struct_0('#skF_4'))
    | k2_struct_0('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2694,c_3537])).

tff(c_3543,plain,(
    k2_struct_0('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_3540])).

tff(c_3545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3000,c_3543])).

tff(c_3546,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3535])).

tff(c_3576,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_3546])).

tff(c_3580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_3576])).

tff(c_3582,plain,(
    r2_hidden(k2_struct_0('#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1845])).

tff(c_3624,plain,(
    ~ r1_tarski('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3582,c_56])).

tff(c_3636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_3624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.16/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.11  
% 5.16/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.11  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 5.16/2.11  
% 5.16/2.11  %Foreground sorts:
% 5.16/2.11  
% 5.16/2.11  
% 5.16/2.11  %Background operators:
% 5.16/2.11  
% 5.16/2.11  
% 5.16/2.11  %Foreground operators:
% 5.16/2.11  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.16/2.11  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.16/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.16/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.16/2.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.16/2.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.16/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.16/2.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.16/2.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.16/2.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.16/2.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.16/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.16/2.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.16/2.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.16/2.11  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.16/2.11  tff('#skF_5', type, '#skF_5': $i).
% 5.16/2.11  tff('#skF_6', type, '#skF_6': $i).
% 5.16/2.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.16/2.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.16/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.16/2.11  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.16/2.11  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.16/2.11  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.16/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.16/2.11  tff('#skF_4', type, '#skF_4': $i).
% 5.16/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.16/2.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.16/2.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.16/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.16/2.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.16/2.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.16/2.11  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.16/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.16/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.16/2.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.16/2.11  
% 5.44/2.13  tff(f_157, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 5.44/2.13  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.44/2.13  tff(f_123, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 5.44/2.13  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.44/2.13  tff(f_101, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.44/2.13  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.44/2.13  tff(f_105, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.44/2.13  tff(f_84, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 5.44/2.13  tff(f_117, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.44/2.13  tff(f_70, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.44/2.13  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.44/2.13  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.44/2.13  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.44/2.13  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.44/2.13  tff(f_129, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.44/2.13  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.44/2.13  tff(f_64, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.44/2.13  tff(f_90, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.44/2.13  tff(c_68, plain, (k1_xboole_0='#skF_6'), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.44/2.13  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.44/2.13  tff(c_91, plain, (![A_10]: (r1_tarski('#skF_6', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_16])).
% 5.44/2.13  tff(c_76, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.44/2.13  tff(c_74, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.44/2.13  tff(c_64, plain, (![A_66]: (v4_pre_topc(k2_struct_0(A_66), A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.44/2.13  tff(c_125, plain, (![A_91]: (v1_xboole_0(A_91) | r2_hidden('#skF_1'(A_91), A_91))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.44/2.13  tff(c_56, plain, (![B_62, A_61]: (~r1_tarski(B_62, A_61) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.44/2.13  tff(c_139, plain, (![A_94]: (~r1_tarski(A_94, '#skF_1'(A_94)) | v1_xboole_0(A_94))), inference(resolution, [status(thm)], [c_125, c_56])).
% 5.44/2.13  tff(c_144, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_91, c_139])).
% 5.44/2.13  tff(c_60, plain, (![A_64]: (l1_struct_0(A_64) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.44/2.13  tff(c_119, plain, (![A_88]: (u1_struct_0(A_88)=k2_struct_0(A_88) | ~l1_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.44/2.13  tff(c_145, plain, (![A_95]: (u1_struct_0(A_95)=k2_struct_0(A_95) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_60, c_119])).
% 5.44/2.13  tff(c_149, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_74, c_145])).
% 5.44/2.13  tff(c_72, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.44/2.13  tff(c_157, plain, (m1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_72])).
% 5.44/2.13  tff(c_48, plain, (![C_53, A_47, B_51]: (r2_hidden(C_53, k3_subset_1(A_47, B_51)) | r2_hidden(C_53, B_51) | ~m1_subset_1(C_53, A_47) | ~m1_subset_1(B_51, k1_zfmisc_1(A_47)) | k1_xboole_0=A_47)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.44/2.13  tff(c_2542, plain, (![C_307, A_308, B_309]: (r2_hidden(C_307, k3_subset_1(A_308, B_309)) | r2_hidden(C_307, B_309) | ~m1_subset_1(C_307, A_308) | ~m1_subset_1(B_309, k1_zfmisc_1(A_308)) | A_308='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_48])).
% 5.44/2.13  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.44/2.13  tff(c_2928, plain, (![A_326, B_327, C_328]: (~v1_xboole_0(k3_subset_1(A_326, B_327)) | r2_hidden(C_328, B_327) | ~m1_subset_1(C_328, A_326) | ~m1_subset_1(B_327, k1_zfmisc_1(A_326)) | A_326='#skF_6')), inference(resolution, [status(thm)], [c_2542, c_2])).
% 5.44/2.13  tff(c_2954, plain, (![B_327]: (~v1_xboole_0(k3_subset_1(k2_struct_0('#skF_4'), B_327)) | r2_hidden('#skF_5', B_327) | ~m1_subset_1(B_327, k1_zfmisc_1(k2_struct_0('#skF_4'))) | k2_struct_0('#skF_4')='#skF_6')), inference(resolution, [status(thm)], [c_157, c_2928])).
% 5.44/2.13  tff(c_2979, plain, (k2_struct_0('#skF_4')='#skF_6'), inference(splitLeft, [status(thm)], [c_2954])).
% 5.44/2.13  tff(c_78, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.44/2.13  tff(c_188, plain, (![A_104]: (~v1_xboole_0(u1_struct_0(A_104)) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.44/2.13  tff(c_191, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_149, c_188])).
% 5.44/2.13  tff(c_192, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_191])).
% 5.44/2.13  tff(c_205, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_192])).
% 5.44/2.13  tff(c_208, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_205])).
% 5.44/2.13  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_208])).
% 5.44/2.13  tff(c_213, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_192])).
% 5.44/2.13  tff(c_2991, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2979, c_213])).
% 5.44/2.13  tff(c_2998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_2991])).
% 5.44/2.13  tff(c_3000, plain, (k2_struct_0('#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_2954])).
% 5.44/2.13  tff(c_46, plain, (![A_46]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.44/2.13  tff(c_88, plain, (![A_46]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_46])).
% 5.44/2.13  tff(c_18, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.44/2.13  tff(c_90, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_6')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_18])).
% 5.44/2.13  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.44/2.13  tff(c_92, plain, (![A_9]: (k3_xboole_0(A_9, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_14])).
% 5.44/2.13  tff(c_268, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k3_xboole_0(A_116, B_117))=k4_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.44/2.13  tff(c_277, plain, (![A_9]: (k5_xboole_0(A_9, '#skF_6')=k4_xboole_0(A_9, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_268])).
% 5.44/2.13  tff(c_280, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_6')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_277])).
% 5.44/2.13  tff(c_1746, plain, (![A_230, B_231]: (k4_xboole_0(A_230, B_231)=k3_subset_1(A_230, B_231) | ~m1_subset_1(B_231, k1_zfmisc_1(A_230)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.44/2.13  tff(c_1760, plain, (![A_46]: (k4_xboole_0(A_46, '#skF_6')=k3_subset_1(A_46, '#skF_6'))), inference(resolution, [status(thm)], [c_88, c_1746])).
% 5.44/2.13  tff(c_1765, plain, (![A_46]: (k3_subset_1(A_46, '#skF_6')=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_280, c_1760])).
% 5.44/2.13  tff(c_2567, plain, (![C_307, A_46]: (r2_hidden(C_307, A_46) | r2_hidden(C_307, '#skF_6') | ~m1_subset_1(C_307, A_46) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_46)) | A_46='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1765, c_2542])).
% 5.44/2.13  tff(c_2593, plain, (![C_310, A_311]: (r2_hidden(C_310, A_311) | r2_hidden(C_310, '#skF_6') | ~m1_subset_1(C_310, A_311) | A_311='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2567])).
% 5.44/2.13  tff(c_2664, plain, (![C_310, A_311]: (~r1_tarski('#skF_6', C_310) | r2_hidden(C_310, A_311) | ~m1_subset_1(C_310, A_311) | A_311='#skF_6')), inference(resolution, [status(thm)], [c_2593, c_56])).
% 5.44/2.13  tff(c_2694, plain, (![C_310, A_311]: (r2_hidden(C_310, A_311) | ~m1_subset_1(C_310, A_311) | A_311='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_2664])).
% 5.44/2.13  tff(c_66, plain, (![A_67]: (v3_pre_topc(k2_struct_0(A_67), A_67) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.44/2.13  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.44/2.13  tff(c_170, plain, (![C_100, A_101]: (r2_hidden(C_100, k1_zfmisc_1(A_101)) | ~r1_tarski(C_100, A_101))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.44/2.13  tff(c_52, plain, (![A_56, B_57]: (m1_subset_1(A_56, B_57) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.44/2.13  tff(c_245, plain, (![C_113, A_114]: (m1_subset_1(C_113, k1_zfmisc_1(A_114)) | ~r1_tarski(C_113, A_114))), inference(resolution, [status(thm)], [c_170, c_52])).
% 5.44/2.13  tff(c_82, plain, (![D_79]: (r2_hidden('#skF_5', D_79) | ~r2_hidden(D_79, '#skF_6') | ~m1_subset_1(D_79, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.44/2.13  tff(c_193, plain, (![D_79]: (r2_hidden('#skF_5', D_79) | ~r2_hidden(D_79, '#skF_6') | ~m1_subset_1(D_79, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_82])).
% 5.44/2.13  tff(c_1831, plain, (![C_237]: (r2_hidden('#skF_5', C_237) | ~r2_hidden(C_237, '#skF_6') | ~r1_tarski(C_237, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_245, c_193])).
% 5.44/2.13  tff(c_1845, plain, (r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~r2_hidden(k2_struct_0('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_10, c_1831])).
% 5.44/2.13  tff(c_1848, plain, (~r2_hidden(k2_struct_0('#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1845])).
% 5.44/2.13  tff(c_184, plain, (![C_100, A_101]: (m1_subset_1(C_100, k1_zfmisc_1(A_101)) | ~r1_tarski(C_100, A_101))), inference(resolution, [status(thm)], [c_170, c_52])).
% 5.44/2.13  tff(c_80, plain, (![D_79]: (r2_hidden(D_79, '#skF_6') | ~r2_hidden('#skF_5', D_79) | ~v4_pre_topc(D_79, '#skF_4') | ~v3_pre_topc(D_79, '#skF_4') | ~m1_subset_1(D_79, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.44/2.13  tff(c_448, plain, (![D_139]: (r2_hidden(D_139, '#skF_6') | ~r2_hidden('#skF_5', D_139) | ~v4_pre_topc(D_139, '#skF_4') | ~v3_pre_topc(D_139, '#skF_4') | ~m1_subset_1(D_139, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_80])).
% 5.44/2.13  tff(c_3469, plain, (![C_352]: (r2_hidden(C_352, '#skF_6') | ~r2_hidden('#skF_5', C_352) | ~v4_pre_topc(C_352, '#skF_4') | ~v3_pre_topc(C_352, '#skF_4') | ~r1_tarski(C_352, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_184, c_448])).
% 5.44/2.13  tff(c_3505, plain, (r2_hidden(k2_struct_0('#skF_4'), '#skF_6') | ~r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_10, c_3469])).
% 5.44/2.13  tff(c_3522, plain, (~r2_hidden('#skF_5', k2_struct_0('#skF_4')) | ~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1848, c_3505])).
% 5.44/2.13  tff(c_3527, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3522])).
% 5.44/2.13  tff(c_3530, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_3527])).
% 5.44/2.13  tff(c_3534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_3530])).
% 5.44/2.13  tff(c_3535, plain, (~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~r2_hidden('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_3522])).
% 5.44/2.13  tff(c_3537, plain, (~r2_hidden('#skF_5', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_3535])).
% 5.44/2.13  tff(c_3540, plain, (~m1_subset_1('#skF_5', k2_struct_0('#skF_4')) | k2_struct_0('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_2694, c_3537])).
% 5.44/2.13  tff(c_3543, plain, (k2_struct_0('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_3540])).
% 5.44/2.13  tff(c_3545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3000, c_3543])).
% 5.44/2.13  tff(c_3546, plain, (~v4_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_3535])).
% 5.44/2.13  tff(c_3576, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_3546])).
% 5.44/2.13  tff(c_3580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_3576])).
% 5.44/2.13  tff(c_3582, plain, (r2_hidden(k2_struct_0('#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_1845])).
% 5.44/2.13  tff(c_3624, plain, (~r1_tarski('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_3582, c_56])).
% 5.44/2.13  tff(c_3636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_3624])).
% 5.44/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.13  
% 5.44/2.13  Inference rules
% 5.44/2.13  ----------------------
% 5.44/2.13  #Ref     : 0
% 5.44/2.13  #Sup     : 706
% 5.44/2.13  #Fact    : 4
% 5.44/2.13  #Define  : 0
% 5.44/2.13  #Split   : 16
% 5.44/2.13  #Chain   : 0
% 5.44/2.13  #Close   : 0
% 5.44/2.13  
% 5.44/2.13  Ordering : KBO
% 5.44/2.13  
% 5.44/2.13  Simplification rules
% 5.44/2.13  ----------------------
% 5.44/2.13  #Subsume      : 92
% 5.44/2.13  #Demod        : 184
% 5.44/2.13  #Tautology    : 153
% 5.44/2.13  #SimpNegUnit  : 64
% 5.44/2.13  #BackRed      : 45
% 5.44/2.13  
% 5.44/2.13  #Partial instantiations: 0
% 5.44/2.13  #Strategies tried      : 1
% 5.44/2.13  
% 5.44/2.13  Timing (in seconds)
% 5.44/2.13  ----------------------
% 5.44/2.13  Preprocessing        : 0.37
% 5.44/2.14  Parsing              : 0.18
% 5.44/2.14  CNF conversion       : 0.03
% 5.44/2.14  Main loop            : 0.83
% 5.44/2.14  Inferencing          : 0.26
% 5.44/2.14  Reduction            : 0.26
% 5.44/2.14  Demodulation         : 0.16
% 5.44/2.14  BG Simplification    : 0.04
% 5.44/2.14  Subsumption          : 0.19
% 5.44/2.14  Abstraction          : 0.04
% 5.44/2.14  MUC search           : 0.00
% 5.44/2.14  Cooper               : 0.00
% 5.44/2.14  Total                : 1.24
% 5.44/2.14  Index Insertion      : 0.00
% 5.44/2.14  Index Deletion       : 0.00
% 5.44/2.14  Index Matching       : 0.00
% 5.44/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
