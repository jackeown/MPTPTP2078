%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:16 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 371 expanded)
%              Number of leaves         :   46 ( 141 expanded)
%              Depth                    :   12
%              Number of atoms          :  243 (1316 expanded)
%              Number of equality atoms :   41 ( 107 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_28,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_32,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_101,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_141,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_122,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_54,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & A != B
        & k6_subset_1(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [A_75,B_76] : k4_xboole_0(A_75,k4_xboole_0(A_75,B_76)) = k3_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_178,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_160])).

tff(c_181,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_178])).

tff(c_314,plain,(
    ! [A_91,B_92,C_93] : k4_xboole_0(k4_xboole_0(A_91,B_92),C_93) = k4_xboole_0(A_91,k2_xboole_0(B_92,C_93)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_647,plain,(
    ! [A_109,C_110] : k4_xboole_0(A_109,k2_xboole_0(A_109,C_110)) = k4_xboole_0(k1_xboole_0,C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_314])).

tff(c_6,plain,(
    ! [A_2,B_3] : r1_tarski(k4_xboole_0(A_2,B_3),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_713,plain,(
    ! [C_113,A_114] : r1_tarski(k4_xboole_0(k1_xboole_0,C_113),A_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_6])).

tff(c_28,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_1'(A_23),A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_127,plain,(
    ! [B_66,A_67] :
      ( ~ r1_tarski(B_66,A_67)
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_131,plain,(
    ! [A_23] :
      ( ~ r1_tarski(A_23,'#skF_1'(A_23))
      | k1_xboole_0 = A_23 ) ),
    inference(resolution,[status(thm)],[c_28,c_127])).

tff(c_752,plain,(
    ! [C_113] : k4_xboole_0(k1_xboole_0,C_113) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_713,c_131])).

tff(c_68,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_93,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_18,plain,(
    ! [A_14] :
      ( v1_zfmisc_1(A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_705,plain,(
    ! [A_111,B_112] :
      ( '#skF_2'(A_111,B_112) != B_112
      | v3_tex_2(B_112,A_111)
      | ~ v2_tex_2(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_708,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_705])).

tff(c_711,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_708])).

tff(c_712,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_711])).

tff(c_968,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_712])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_62,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_74,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_94,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_74])).

tff(c_1313,plain,(
    ! [B_133,A_134] :
      ( v2_tex_2(B_133,A_134)
      | ~ v1_zfmisc_1(B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | v1_xboole_0(B_133)
      | ~ l1_pre_topc(A_134)
      | ~ v2_tdlat_3(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1316,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1313])).

tff(c_1319,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_94,c_1316])).

tff(c_1321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_968,c_1319])).

tff(c_1322,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_712])).

tff(c_1323,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_712])).

tff(c_867,plain,(
    ! [B_117,A_118] :
      ( r1_tarski(B_117,'#skF_2'(A_118,B_117))
      | v3_tex_2(B_117,A_118)
      | ~ v2_tex_2(B_117,A_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_869,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_867])).

tff(c_872,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_869])).

tff(c_873,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_872])).

tff(c_1325,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1323,c_873])).

tff(c_50,plain,(
    ! [B_48,A_46] :
      ( B_48 = A_46
      | ~ r1_tarski(A_46,B_48)
      | ~ v1_zfmisc_1(B_48)
      | v1_xboole_0(B_48)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1328,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1325,c_50])).

tff(c_1334,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1322,c_1328])).

tff(c_1565,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1334])).

tff(c_1569,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_1565])).

tff(c_1445,plain,(
    ! [A_137,B_138] :
      ( v2_tex_2('#skF_2'(A_137,B_138),A_137)
      | v3_tex_2(B_138,A_137)
      | ~ v2_tex_2(B_138,A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1447,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1445])).

tff(c_1450,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1323,c_1447])).

tff(c_1451,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_1450])).

tff(c_42,plain,(
    ! [A_34,B_40] :
      ( m1_subset_1('#skF_2'(A_34,B_40),k1_zfmisc_1(u1_struct_0(A_34)))
      | v3_tex_2(B_40,A_34)
      | ~ v2_tex_2(B_40,A_34)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2006,plain,(
    ! [B_154,A_155] :
      ( v1_zfmisc_1(B_154)
      | ~ v2_tex_2(B_154,A_155)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_155)))
      | v1_xboole_0(B_154)
      | ~ l1_pre_topc(A_155)
      | ~ v2_tdlat_3(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_12799,plain,(
    ! [A_300,B_301] :
      ( v1_zfmisc_1('#skF_2'(A_300,B_301))
      | ~ v2_tex_2('#skF_2'(A_300,B_301),A_300)
      | v1_xboole_0('#skF_2'(A_300,B_301))
      | ~ v2_tdlat_3(A_300)
      | ~ v2_pre_topc(A_300)
      | v2_struct_0(A_300)
      | v3_tex_2(B_301,A_300)
      | ~ v2_tex_2(B_301,A_300)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ l1_pre_topc(A_300) ) ),
    inference(resolution,[status(thm)],[c_42,c_2006])).

tff(c_12803,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1451,c_12799])).

tff(c_12807,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1323,c_64,c_62,c_12803])).

tff(c_12809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_66,c_1569,c_1565,c_12807])).

tff(c_12810,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1334])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_116,plain,(
    ! [B_62,A_63] :
      ( ~ v1_xboole_0(B_62)
      | B_62 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_119,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_2,c_116])).

tff(c_12817,plain,(
    '#skF_2'('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12810,c_119])).

tff(c_22,plain,(
    ! [A_17,B_18] : k6_subset_1(A_17,B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [B_45,A_44] :
      ( k6_subset_1(B_45,A_44) != k1_xboole_0
      | B_45 = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_75,plain,(
    ! [B_45,A_44] :
      ( k4_xboole_0(B_45,A_44) != k1_xboole_0
      | B_45 = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_48])).

tff(c_1331,plain,
    ( k4_xboole_0('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0
    | '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1325,c_75])).

tff(c_1337,plain,(
    k4_xboole_0('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1322,c_1331])).

tff(c_12822,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12817,c_1337])).

tff(c_12828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_12822])).

tff(c_12829,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_12830,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_13823,plain,(
    ! [B_365,A_366] :
      ( v2_tex_2(B_365,A_366)
      | ~ v3_tex_2(B_365,A_366)
      | ~ m1_subset_1(B_365,k1_zfmisc_1(u1_struct_0(A_366)))
      | ~ l1_pre_topc(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_13826,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_13823])).

tff(c_13829,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_12830,c_13826])).

tff(c_14395,plain,(
    ! [B_384,A_385] :
      ( v1_zfmisc_1(B_384)
      | ~ v2_tex_2(B_384,A_385)
      | ~ m1_subset_1(B_384,k1_zfmisc_1(u1_struct_0(A_385)))
      | v1_xboole_0(B_384)
      | ~ l1_pre_topc(A_385)
      | ~ v2_tdlat_3(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_14398,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_14395])).

tff(c_14401,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_13829,c_14398])).

tff(c_14403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_12829,c_14401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:31:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.11/2.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.63  
% 7.11/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.63  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 7.11/2.63  
% 7.11/2.63  %Foreground sorts:
% 7.11/2.63  
% 7.11/2.63  
% 7.11/2.63  %Background operators:
% 7.11/2.63  
% 7.11/2.63  
% 7.11/2.63  %Foreground operators:
% 7.11/2.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.11/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.11/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.11/2.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.11/2.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.11/2.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.11/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.11/2.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.11/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.11/2.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.11/2.63  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.11/2.63  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.11/2.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.11/2.63  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.11/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.11/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.11/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.11/2.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.11/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.11/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.11/2.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.11/2.63  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 7.11/2.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.11/2.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.11/2.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.11/2.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.11/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.11/2.63  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 7.11/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.11/2.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.11/2.63  
% 7.11/2.65  tff(f_161, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 7.11/2.65  tff(f_28, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 7.11/2.65  tff(f_32, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.11/2.65  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.11/2.65  tff(f_34, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.11/2.65  tff(f_30, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.11/2.65  tff(f_77, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 7.11/2.65  tff(f_61, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.11/2.65  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 7.11/2.65  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 7.11/2.65  tff(f_141, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 7.11/2.65  tff(f_122, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 7.11/2.65  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.11/2.65  tff(f_44, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 7.11/2.65  tff(f_54, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.11/2.65  tff(f_109, axiom, (![A, B]: ~((r1_tarski(A, B) & ~(A = B)) & (k6_subset_1(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l48_tex_2)).
% 7.11/2.65  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.11/2.65  tff(c_58, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.11/2.65  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 7.11/2.65  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.11/2.65  tff(c_160, plain, (![A_75, B_76]: (k4_xboole_0(A_75, k4_xboole_0(A_75, B_76))=k3_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.11/2.65  tff(c_178, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_160])).
% 7.11/2.65  tff(c_181, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_178])).
% 7.11/2.65  tff(c_314, plain, (![A_91, B_92, C_93]: (k4_xboole_0(k4_xboole_0(A_91, B_92), C_93)=k4_xboole_0(A_91, k2_xboole_0(B_92, C_93)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.11/2.65  tff(c_647, plain, (![A_109, C_110]: (k4_xboole_0(A_109, k2_xboole_0(A_109, C_110))=k4_xboole_0(k1_xboole_0, C_110))), inference(superposition, [status(thm), theory('equality')], [c_181, c_314])).
% 7.11/2.65  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(k4_xboole_0(A_2, B_3), A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.11/2.65  tff(c_713, plain, (![C_113, A_114]: (r1_tarski(k4_xboole_0(k1_xboole_0, C_113), A_114))), inference(superposition, [status(thm), theory('equality')], [c_647, c_6])).
% 7.11/2.65  tff(c_28, plain, (![A_23]: (r2_hidden('#skF_1'(A_23), A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.11/2.65  tff(c_127, plain, (![B_66, A_67]: (~r1_tarski(B_66, A_67) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.11/2.65  tff(c_131, plain, (![A_23]: (~r1_tarski(A_23, '#skF_1'(A_23)) | k1_xboole_0=A_23)), inference(resolution, [status(thm)], [c_28, c_127])).
% 7.11/2.65  tff(c_752, plain, (![C_113]: (k4_xboole_0(k1_xboole_0, C_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_713, c_131])).
% 7.11/2.65  tff(c_68, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.11/2.65  tff(c_93, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 7.11/2.65  tff(c_18, plain, (![A_14]: (v1_zfmisc_1(A_14) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.11/2.65  tff(c_60, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.11/2.65  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.11/2.65  tff(c_705, plain, (![A_111, B_112]: ('#skF_2'(A_111, B_112)!=B_112 | v3_tex_2(B_112, A_111) | ~v2_tex_2(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.11/2.65  tff(c_708, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_56, c_705])).
% 7.11/2.65  tff(c_711, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_708])).
% 7.11/2.65  tff(c_712, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_93, c_711])).
% 7.11/2.65  tff(c_968, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_712])).
% 7.11/2.65  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.11/2.65  tff(c_62, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.11/2.65  tff(c_74, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.11/2.65  tff(c_94, plain, (v1_zfmisc_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_93, c_74])).
% 7.11/2.65  tff(c_1313, plain, (![B_133, A_134]: (v2_tex_2(B_133, A_134) | ~v1_zfmisc_1(B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_134))) | v1_xboole_0(B_133) | ~l1_pre_topc(A_134) | ~v2_tdlat_3(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.11/2.65  tff(c_1316, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1313])).
% 7.11/2.65  tff(c_1319, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_94, c_1316])).
% 7.11/2.65  tff(c_1321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_968, c_1319])).
% 7.11/2.65  tff(c_1322, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_712])).
% 7.11/2.65  tff(c_1323, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_712])).
% 7.11/2.65  tff(c_867, plain, (![B_117, A_118]: (r1_tarski(B_117, '#skF_2'(A_118, B_117)) | v3_tex_2(B_117, A_118) | ~v2_tex_2(B_117, A_118) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.11/2.65  tff(c_869, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_56, c_867])).
% 7.11/2.65  tff(c_872, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_869])).
% 7.11/2.65  tff(c_873, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_93, c_872])).
% 7.11/2.65  tff(c_1325, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1323, c_873])).
% 7.11/2.65  tff(c_50, plain, (![B_48, A_46]: (B_48=A_46 | ~r1_tarski(A_46, B_48) | ~v1_zfmisc_1(B_48) | v1_xboole_0(B_48) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.11/2.65  tff(c_1328, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1325, c_50])).
% 7.11/2.65  tff(c_1334, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_1322, c_1328])).
% 7.11/2.65  tff(c_1565, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1334])).
% 7.11/2.65  tff(c_1569, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_1565])).
% 7.11/2.65  tff(c_1445, plain, (![A_137, B_138]: (v2_tex_2('#skF_2'(A_137, B_138), A_137) | v3_tex_2(B_138, A_137) | ~v2_tex_2(B_138, A_137) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.11/2.65  tff(c_1447, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1445])).
% 7.11/2.65  tff(c_1450, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1323, c_1447])).
% 7.11/2.65  tff(c_1451, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_93, c_1450])).
% 7.11/2.65  tff(c_42, plain, (![A_34, B_40]: (m1_subset_1('#skF_2'(A_34, B_40), k1_zfmisc_1(u1_struct_0(A_34))) | v3_tex_2(B_40, A_34) | ~v2_tex_2(B_40, A_34) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.11/2.65  tff(c_2006, plain, (![B_154, A_155]: (v1_zfmisc_1(B_154) | ~v2_tex_2(B_154, A_155) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_155))) | v1_xboole_0(B_154) | ~l1_pre_topc(A_155) | ~v2_tdlat_3(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.11/2.65  tff(c_12799, plain, (![A_300, B_301]: (v1_zfmisc_1('#skF_2'(A_300, B_301)) | ~v2_tex_2('#skF_2'(A_300, B_301), A_300) | v1_xboole_0('#skF_2'(A_300, B_301)) | ~v2_tdlat_3(A_300) | ~v2_pre_topc(A_300) | v2_struct_0(A_300) | v3_tex_2(B_301, A_300) | ~v2_tex_2(B_301, A_300) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_300))) | ~l1_pre_topc(A_300))), inference(resolution, [status(thm)], [c_42, c_2006])).
% 7.11/2.65  tff(c_12803, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1451, c_12799])).
% 7.11/2.65  tff(c_12807, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1323, c_64, c_62, c_12803])).
% 7.11/2.65  tff(c_12809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_66, c_1569, c_1565, c_12807])).
% 7.11/2.65  tff(c_12810, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1334])).
% 7.11/2.65  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.11/2.65  tff(c_116, plain, (![B_62, A_63]: (~v1_xboole_0(B_62) | B_62=A_63 | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.11/2.65  tff(c_119, plain, (![A_63]: (k1_xboole_0=A_63 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_2, c_116])).
% 7.11/2.65  tff(c_12817, plain, ('#skF_2'('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_12810, c_119])).
% 7.11/2.65  tff(c_22, plain, (![A_17, B_18]: (k6_subset_1(A_17, B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.11/2.65  tff(c_48, plain, (![B_45, A_44]: (k6_subset_1(B_45, A_44)!=k1_xboole_0 | B_45=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.11/2.65  tff(c_75, plain, (![B_45, A_44]: (k4_xboole_0(B_45, A_44)!=k1_xboole_0 | B_45=A_44 | ~r1_tarski(A_44, B_45))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_48])).
% 7.11/2.65  tff(c_1331, plain, (k4_xboole_0('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0 | '#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_1325, c_75])).
% 7.11/2.65  tff(c_1337, plain, (k4_xboole_0('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1322, c_1331])).
% 7.11/2.65  tff(c_12822, plain, (k4_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12817, c_1337])).
% 7.11/2.65  tff(c_12828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_752, c_12822])).
% 7.11/2.65  tff(c_12829, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 7.11/2.65  tff(c_12830, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 7.11/2.65  tff(c_13823, plain, (![B_365, A_366]: (v2_tex_2(B_365, A_366) | ~v3_tex_2(B_365, A_366) | ~m1_subset_1(B_365, k1_zfmisc_1(u1_struct_0(A_366))) | ~l1_pre_topc(A_366))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.11/2.65  tff(c_13826, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_56, c_13823])).
% 7.11/2.65  tff(c_13829, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_12830, c_13826])).
% 7.11/2.65  tff(c_14395, plain, (![B_384, A_385]: (v1_zfmisc_1(B_384) | ~v2_tex_2(B_384, A_385) | ~m1_subset_1(B_384, k1_zfmisc_1(u1_struct_0(A_385))) | v1_xboole_0(B_384) | ~l1_pre_topc(A_385) | ~v2_tdlat_3(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.11/2.65  tff(c_14398, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_14395])).
% 7.11/2.65  tff(c_14401, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_13829, c_14398])).
% 7.11/2.65  tff(c_14403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_12829, c_14401])).
% 7.11/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.11/2.65  
% 7.11/2.65  Inference rules
% 7.11/2.65  ----------------------
% 7.11/2.65  #Ref     : 0
% 7.11/2.65  #Sup     : 3486
% 7.11/2.65  #Fact    : 0
% 7.11/2.65  #Define  : 0
% 7.11/2.65  #Split   : 5
% 7.11/2.65  #Chain   : 0
% 7.11/2.65  #Close   : 0
% 7.11/2.65  
% 7.11/2.65  Ordering : KBO
% 7.11/2.65  
% 7.11/2.65  Simplification rules
% 7.11/2.65  ----------------------
% 7.11/2.65  #Subsume      : 251
% 7.11/2.65  #Demod        : 3040
% 7.11/2.65  #Tautology    : 2160
% 7.11/2.65  #SimpNegUnit  : 16
% 7.11/2.65  #BackRed      : 12
% 7.11/2.65  
% 7.11/2.65  #Partial instantiations: 0
% 7.11/2.65  #Strategies tried      : 1
% 7.11/2.65  
% 7.11/2.65  Timing (in seconds)
% 7.11/2.65  ----------------------
% 7.11/2.65  Preprocessing        : 0.33
% 7.11/2.65  Parsing              : 0.18
% 7.11/2.65  CNF conversion       : 0.02
% 7.11/2.65  Main loop            : 1.54
% 7.11/2.65  Inferencing          : 0.43
% 7.11/2.65  Reduction            : 0.71
% 7.11/2.65  Demodulation         : 0.58
% 7.11/2.65  BG Simplification    : 0.06
% 7.11/2.65  Subsumption          : 0.25
% 7.11/2.65  Abstraction          : 0.08
% 7.11/2.65  MUC search           : 0.00
% 7.11/2.65  Cooper               : 0.00
% 7.11/2.65  Total                : 1.91
% 7.11/2.65  Index Insertion      : 0.00
% 7.11/2.65  Index Deletion       : 0.00
% 7.11/2.65  Index Matching       : 0.00
% 7.11/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
