%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:01 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 110 expanded)
%              Number of leaves         :   39 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 ( 240 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    v3_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1('#skF_2'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [A_61,B_62] :
      ( k6_domain_1(A_61,B_62) = k1_tarski(B_62)
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_158,plain,(
    ! [A_10] :
      ( k6_domain_1(A_10,'#skF_2'(A_10)) = k1_tarski('#skF_2'(A_10))
      | v1_xboole_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_151])).

tff(c_377,plain,(
    ! [A_90,B_91] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_90),B_91),A_90)
      | ~ m1_subset_1(B_91,u1_struct_0(A_90))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_381,plain,(
    ! [A_90] :
      ( v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_90))),A_90)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_90)),u1_struct_0(A_90))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90)
      | v1_xboole_0(u1_struct_0(A_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_377])).

tff(c_881,plain,(
    ! [A_138] :
      ( v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_138))),A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138)
      | v1_xboole_0(u1_struct_0(A_138)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_381])).

tff(c_50,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_58,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_58])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_6') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),B_9) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_92,plain,(
    ! [A_48,B_49] : k2_xboole_0(k1_tarski(A_48),B_49) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12])).

tff(c_96,plain,(
    ! [A_48] : k1_tarski(A_48) != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_92])).

tff(c_220,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k6_domain_1(A_73,B_74),k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_233,plain,(
    ! [A_10] :
      ( m1_subset_1(k1_tarski('#skF_2'(A_10)),k1_zfmisc_1(A_10))
      | ~ m1_subset_1('#skF_2'(A_10),A_10)
      | v1_xboole_0(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_220])).

tff(c_240,plain,(
    ! [A_10] :
      ( m1_subset_1(k1_tarski('#skF_2'(A_10)),k1_zfmisc_1(A_10))
      | v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_233])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [A_12] : m1_subset_1('#skF_6',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_16])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [A_7] : r1_tarski('#skF_6',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10])).

tff(c_679,plain,(
    ! [C_127,B_128,A_129] :
      ( C_127 = B_128
      | ~ r1_tarski(B_128,C_127)
      | ~ v2_tex_2(C_127,A_129)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ v3_tex_2(B_128,A_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_681,plain,(
    ! [A_7,A_129] :
      ( A_7 = '#skF_6'
      | ~ v2_tex_2(A_7,A_129)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ v3_tex_2('#skF_6',A_129)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(resolution,[status(thm)],[c_64,c_679])).

tff(c_715,plain,(
    ! [A_130,A_131] :
      ( A_130 = '#skF_6'
      | ~ v2_tex_2(A_130,A_131)
      | ~ m1_subset_1(A_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v3_tex_2('#skF_6',A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_681])).

tff(c_729,plain,(
    ! [A_131] :
      ( k1_tarski('#skF_2'(u1_struct_0(A_131))) = '#skF_6'
      | ~ v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_131))),A_131)
      | ~ v3_tex_2('#skF_6',A_131)
      | ~ l1_pre_topc(A_131)
      | v1_xboole_0(u1_struct_0(A_131)) ) ),
    inference(resolution,[status(thm)],[c_240,c_715])).

tff(c_751,plain,(
    ! [A_131] :
      ( ~ v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_131))),A_131)
      | ~ v3_tex_2('#skF_6',A_131)
      | ~ l1_pre_topc(A_131)
      | v1_xboole_0(u1_struct_0(A_131)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_729])).

tff(c_886,plain,(
    ! [A_139] :
      ( ~ v3_tex_2('#skF_6',A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139)
      | v1_xboole_0(u1_struct_0(A_139)) ) ),
    inference(resolution,[status(thm)],[c_881,c_751])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_255,plain,(
    ! [A_76] :
      ( m1_subset_1('#skF_3'(A_76),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ! [C_18,B_17,A_16] :
      ( ~ v1_xboole_0(C_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(C_18))
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_371,plain,(
    ! [A_88,A_89] :
      ( ~ v1_xboole_0(u1_struct_0(A_88))
      | ~ r2_hidden(A_89,'#skF_3'(A_88))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_255,c_20])).

tff(c_376,plain,(
    ! [A_88] :
      ( ~ v1_xboole_0(u1_struct_0(A_88))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88)
      | v1_xboole_0('#skF_3'(A_88)) ) ),
    inference(resolution,[status(thm)],[c_4,c_371])).

tff(c_895,plain,(
    ! [A_140] :
      ( v1_xboole_0('#skF_3'(A_140))
      | ~ v3_tex_2('#skF_6',A_140)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_886,c_376])).

tff(c_24,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0('#skF_3'(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_904,plain,(
    ! [A_141] :
      ( ~ v3_tex_2('#skF_6',A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_895,c_24])).

tff(c_910,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_904])).

tff(c_914,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_910])).

tff(c_916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_914])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:20:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.50  
% 3.15/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.50  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 3.15/1.50  
% 3.15/1.50  %Foreground sorts:
% 3.15/1.50  
% 3.15/1.50  
% 3.15/1.50  %Background operators:
% 3.15/1.50  
% 3.15/1.50  
% 3.15/1.50  %Foreground operators:
% 3.15/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.15/1.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.15/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.15/1.50  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.15/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.50  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.15/1.50  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.15/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.50  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.50  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.15/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.15/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.15/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.15/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.50  
% 3.15/1.52  tff(f_135, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 3.15/1.52  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.15/1.52  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.15/1.52  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 3.15/1.52  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.15/1.52  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.15/1.52  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.15/1.52  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.15/1.52  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.15/1.52  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/1.52  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 3.15/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.15/1.52  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 3.15/1.52  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.15/1.52  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.15/1.52  tff(c_54, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.15/1.52  tff(c_52, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.15/1.52  tff(c_46, plain, (v3_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.15/1.52  tff(c_14, plain, (![A_10]: (m1_subset_1('#skF_2'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.15/1.52  tff(c_151, plain, (![A_61, B_62]: (k6_domain_1(A_61, B_62)=k1_tarski(B_62) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.15/1.52  tff(c_158, plain, (![A_10]: (k6_domain_1(A_10, '#skF_2'(A_10))=k1_tarski('#skF_2'(A_10)) | v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_14, c_151])).
% 3.15/1.52  tff(c_377, plain, (![A_90, B_91]: (v2_tex_2(k6_domain_1(u1_struct_0(A_90), B_91), A_90) | ~m1_subset_1(B_91, u1_struct_0(A_90)) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.15/1.52  tff(c_381, plain, (![A_90]: (v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_90))), A_90) | ~m1_subset_1('#skF_2'(u1_struct_0(A_90)), u1_struct_0(A_90)) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90) | v1_xboole_0(u1_struct_0(A_90)))), inference(superposition, [status(thm), theory('equality')], [c_158, c_377])).
% 3.15/1.52  tff(c_881, plain, (![A_138]: (v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_138))), A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138) | v1_xboole_0(u1_struct_0(A_138)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_381])).
% 3.15/1.52  tff(c_50, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.15/1.52  tff(c_58, plain, (![A_40]: (k1_xboole_0=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.52  tff(c_62, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_50, c_58])).
% 3.15/1.52  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.52  tff(c_70, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_6')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8])).
% 3.15/1.52  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.15/1.52  tff(c_92, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), B_49)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12])).
% 3.15/1.52  tff(c_96, plain, (![A_48]: (k1_tarski(A_48)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_70, c_92])).
% 3.15/1.52  tff(c_220, plain, (![A_73, B_74]: (m1_subset_1(k6_domain_1(A_73, B_74), k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.15/1.52  tff(c_233, plain, (![A_10]: (m1_subset_1(k1_tarski('#skF_2'(A_10)), k1_zfmisc_1(A_10)) | ~m1_subset_1('#skF_2'(A_10), A_10) | v1_xboole_0(A_10) | v1_xboole_0(A_10))), inference(superposition, [status(thm), theory('equality')], [c_158, c_220])).
% 3.15/1.52  tff(c_240, plain, (![A_10]: (m1_subset_1(k1_tarski('#skF_2'(A_10)), k1_zfmisc_1(A_10)) | v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_233])).
% 3.15/1.52  tff(c_16, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.15/1.52  tff(c_80, plain, (![A_12]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_16])).
% 3.15/1.52  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.52  tff(c_64, plain, (![A_7]: (r1_tarski('#skF_6', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10])).
% 3.15/1.52  tff(c_679, plain, (![C_127, B_128, A_129]: (C_127=B_128 | ~r1_tarski(B_128, C_127) | ~v2_tex_2(C_127, A_129) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_129))) | ~v3_tex_2(B_128, A_129) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.15/1.52  tff(c_681, plain, (![A_7, A_129]: (A_7='#skF_6' | ~v2_tex_2(A_7, A_129) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_129))) | ~v3_tex_2('#skF_6', A_129) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(resolution, [status(thm)], [c_64, c_679])).
% 3.15/1.52  tff(c_715, plain, (![A_130, A_131]: (A_130='#skF_6' | ~v2_tex_2(A_130, A_131) | ~m1_subset_1(A_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~v3_tex_2('#skF_6', A_131) | ~l1_pre_topc(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_681])).
% 3.15/1.52  tff(c_729, plain, (![A_131]: (k1_tarski('#skF_2'(u1_struct_0(A_131)))='#skF_6' | ~v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_131))), A_131) | ~v3_tex_2('#skF_6', A_131) | ~l1_pre_topc(A_131) | v1_xboole_0(u1_struct_0(A_131)))), inference(resolution, [status(thm)], [c_240, c_715])).
% 3.15/1.52  tff(c_751, plain, (![A_131]: (~v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_131))), A_131) | ~v3_tex_2('#skF_6', A_131) | ~l1_pre_topc(A_131) | v1_xboole_0(u1_struct_0(A_131)))), inference(negUnitSimplification, [status(thm)], [c_96, c_729])).
% 3.15/1.52  tff(c_886, plain, (![A_139]: (~v3_tex_2('#skF_6', A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139) | v1_xboole_0(u1_struct_0(A_139)))), inference(resolution, [status(thm)], [c_881, c_751])).
% 3.15/1.52  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.52  tff(c_255, plain, (![A_76]: (m1_subset_1('#skF_3'(A_76), k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.15/1.52  tff(c_20, plain, (![C_18, B_17, A_16]: (~v1_xboole_0(C_18) | ~m1_subset_1(B_17, k1_zfmisc_1(C_18)) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.52  tff(c_371, plain, (![A_88, A_89]: (~v1_xboole_0(u1_struct_0(A_88)) | ~r2_hidden(A_89, '#skF_3'(A_88)) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_255, c_20])).
% 3.15/1.52  tff(c_376, plain, (![A_88]: (~v1_xboole_0(u1_struct_0(A_88)) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88) | v1_xboole_0('#skF_3'(A_88)))), inference(resolution, [status(thm)], [c_4, c_371])).
% 3.15/1.52  tff(c_895, plain, (![A_140]: (v1_xboole_0('#skF_3'(A_140)) | ~v3_tex_2('#skF_6', A_140) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_886, c_376])).
% 3.15/1.52  tff(c_24, plain, (![A_19]: (~v1_xboole_0('#skF_3'(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.15/1.52  tff(c_904, plain, (![A_141]: (~v3_tex_2('#skF_6', A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(resolution, [status(thm)], [c_895, c_24])).
% 3.15/1.52  tff(c_910, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_904])).
% 3.15/1.52  tff(c_914, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_910])).
% 3.15/1.52  tff(c_916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_914])).
% 3.15/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.52  
% 3.15/1.52  Inference rules
% 3.15/1.52  ----------------------
% 3.15/1.52  #Ref     : 0
% 3.15/1.52  #Sup     : 192
% 3.15/1.52  #Fact    : 0
% 3.15/1.52  #Define  : 0
% 3.15/1.52  #Split   : 3
% 3.15/1.52  #Chain   : 0
% 3.15/1.52  #Close   : 0
% 3.15/1.52  
% 3.15/1.52  Ordering : KBO
% 3.15/1.52  
% 3.15/1.52  Simplification rules
% 3.15/1.52  ----------------------
% 3.15/1.52  #Subsume      : 23
% 3.15/1.52  #Demod        : 39
% 3.15/1.52  #Tautology    : 39
% 3.15/1.52  #SimpNegUnit  : 4
% 3.15/1.52  #BackRed      : 5
% 3.15/1.52  
% 3.15/1.52  #Partial instantiations: 0
% 3.15/1.52  #Strategies tried      : 1
% 3.15/1.52  
% 3.15/1.52  Timing (in seconds)
% 3.15/1.52  ----------------------
% 3.15/1.52  Preprocessing        : 0.32
% 3.15/1.52  Parsing              : 0.17
% 3.15/1.52  CNF conversion       : 0.02
% 3.15/1.52  Main loop            : 0.43
% 3.15/1.52  Inferencing          : 0.16
% 3.15/1.52  Reduction            : 0.13
% 3.15/1.52  Demodulation         : 0.08
% 3.15/1.52  BG Simplification    : 0.02
% 3.15/1.52  Subsumption          : 0.09
% 3.15/1.52  Abstraction          : 0.02
% 3.15/1.52  MUC search           : 0.00
% 3.15/1.52  Cooper               : 0.00
% 3.15/1.52  Total                : 0.79
% 3.15/1.52  Index Insertion      : 0.00
% 3.15/1.52  Index Deletion       : 0.00
% 3.15/1.52  Index Matching       : 0.00
% 3.15/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
