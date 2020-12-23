%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:04 EST 2020

% Result     : Theorem 6.30s
% Output     : CNFRefutation 6.30s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 298 expanded)
%              Number of leaves         :   41 ( 125 expanded)
%              Depth                    :   12
%              Number of atoms          :  205 ( 872 expanded)
%              Number of equality atoms :   64 ( 127 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v1_tops_1(B,A)
                & v2_tex_2(B,A) )
             => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_94,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_58,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_60,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1214,plain,(
    ! [A_147,B_148] :
      ( '#skF_1'(A_147,B_148) != B_148
      | v3_tex_2(B_148,A_147)
      | ~ v2_tex_2(B_148,A_147)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1225,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1214])).

tff(c_1234,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_1225])).

tff(c_1235,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1234])).

tff(c_1618,plain,(
    ! [B_169,A_170] :
      ( r1_tarski(B_169,'#skF_1'(A_170,B_169))
      | v3_tex_2(B_169,A_170)
      | ~ v2_tex_2(B_169,A_170)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1626,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1618])).

tff(c_1634,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_1626])).

tff(c_1635,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1634])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1659,plain,(
    k4_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1635,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_14,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_71,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_314,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k3_subset_1(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_320,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_subset_1(A_10,A_10) ),
    inference(resolution,[status(thm)],[c_71,c_314])).

tff(c_329,plain,(
    ! [A_10] : k3_subset_1(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_320])).

tff(c_507,plain,(
    ! [A_96,B_97] :
      ( k3_subset_1(A_96,k3_subset_1(A_96,B_97)) = B_97
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_511,plain,(
    ! [A_10] : k3_subset_1(A_10,k3_subset_1(A_10,A_10)) = A_10 ),
    inference(resolution,[status(thm)],[c_71,c_507])).

tff(c_518,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_511])).

tff(c_24,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_341,plain,(
    ! [A_77] : k4_xboole_0(A_77,k1_xboole_0) = k3_subset_1(A_77,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_314])).

tff(c_12,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_347,plain,(
    ! [A_77] : k4_xboole_0(A_77,k3_subset_1(A_77,k1_xboole_0)) = k3_xboole_0(A_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_12])).

tff(c_534,plain,(
    ! [A_77] : k4_xboole_0(A_77,A_77) = k3_xboole_0(A_77,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_347])).

tff(c_539,plain,(
    ! [A_77] : k3_xboole_0(A_77,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_534])).

tff(c_1811,plain,(
    ! [A_176,B_177] :
      ( m1_subset_1('#skF_1'(A_176,B_177),k1_zfmisc_1(u1_struct_0(A_176)))
      | v3_tex_2(B_177,A_176)
      | ~ v2_tex_2(B_177,A_176)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3307,plain,(
    ! [A_225,B_226] :
      ( r1_tarski('#skF_1'(A_225,B_226),u1_struct_0(A_225))
      | v3_tex_2(B_226,A_225)
      | ~ v2_tex_2(B_226,A_225)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_pre_topc(A_225) ) ),
    inference(resolution,[status(thm)],[c_1811,c_28])).

tff(c_3736,plain,(
    ! [A_240,B_241] :
      ( k4_xboole_0('#skF_1'(A_240,B_241),u1_struct_0(A_240)) = k1_xboole_0
      | v3_tex_2(B_241,A_240)
      | ~ v2_tex_2(B_241,A_240)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240) ) ),
    inference(resolution,[status(thm)],[c_3307,c_10])).

tff(c_3748,plain,
    ( k4_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = k1_xboole_0
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_3736])).

tff(c_3758,plain,
    ( k4_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = k1_xboole_0
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_3748])).

tff(c_3759,plain,(
    k4_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3758])).

tff(c_1541,plain,(
    ! [A_160,B_161] :
      ( v2_tex_2('#skF_1'(A_160,B_161),A_160)
      | v3_tex_2(B_161,A_160)
      | ~ v2_tex_2(B_161,A_160)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1549,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1541])).

tff(c_1557,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_1549])).

tff(c_1558,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1557])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_521,plain,(
    ! [A_98,B_99,C_100] :
      ( k9_subset_1(A_98,B_99,C_100) = k3_xboole_0(B_99,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_531,plain,(
    ! [A_10,B_99] : k9_subset_1(A_10,B_99,A_10) = k3_xboole_0(B_99,A_10) ),
    inference(resolution,[status(thm)],[c_71,c_521])).

tff(c_62,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_819,plain,(
    ! [A_121,B_122] :
      ( k2_pre_topc(A_121,B_122) = u1_struct_0(A_121)
      | ~ v1_tops_1(B_122,A_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_830,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_819])).

tff(c_839,plain,(
    k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_830])).

tff(c_2782,plain,(
    ! [A_214,B_215,C_216] :
      ( k9_subset_1(u1_struct_0(A_214),B_215,k2_pre_topc(A_214,C_216)) = C_216
      | ~ r1_tarski(C_216,B_215)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ v2_tex_2(B_215,A_214)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2794,plain,(
    ! [B_215] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_215,k2_pre_topc('#skF_3','#skF_4')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_215)
      | ~ v2_tex_2(B_215,'#skF_3')
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_2782])).

tff(c_2804,plain,(
    ! [B_215] :
      ( k3_xboole_0(B_215,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_215)
      | ~ v2_tex_2(B_215,'#skF_3')
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_531,c_839,c_2794])).

tff(c_2809,plain,(
    ! [B_217] :
      ( k3_xboole_0(B_217,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_217)
      | ~ v2_tex_2(B_217,'#skF_3')
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2804])).

tff(c_2890,plain,(
    ! [A_219] :
      ( k3_xboole_0(A_219,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_219)
      | ~ v2_tex_2(A_219,'#skF_3')
      | ~ r1_tarski(A_219,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_2809])).

tff(c_2924,plain,(
    ! [A_3] :
      ( k3_xboole_0(A_3,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_3)
      | ~ v2_tex_2(A_3,'#skF_3')
      | k4_xboole_0(A_3,u1_struct_0('#skF_3')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_2890])).

tff(c_3778,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3759,c_2924])).

tff(c_3824,plain,(
    k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1635,c_3778])).

tff(c_206,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_209,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,k4_xboole_0(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_12])).

tff(c_158,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_464,plain,(
    ! [B_89,A_90] :
      ( B_89 = A_90
      | ~ r1_tarski(B_89,A_90)
      | k4_xboole_0(A_90,B_89) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_158])).

tff(c_920,plain,(
    ! [B_127,A_128] :
      ( B_127 = A_128
      | k4_xboole_0(B_127,A_128) != k1_xboole_0
      | k4_xboole_0(A_128,B_127) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_464])).

tff(c_922,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = A_69
      | k3_xboole_0(A_69,k4_xboole_0(A_69,B_70)) != k1_xboole_0
      | k4_xboole_0(k3_xboole_0(A_69,B_70),A_69) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_920])).

tff(c_3858,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | k3_xboole_0('#skF_1'('#skF_3','#skF_4'),k4_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3'))) != k1_xboole_0
    | k4_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3824,c_922])).

tff(c_3871,plain,(
    '#skF_1'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1659,c_539,c_3759,c_3824,c_3858])).

tff(c_3873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1235,c_3871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.30/2.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.62  
% 6.30/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.62  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.30/2.62  
% 6.30/2.62  %Foreground sorts:
% 6.30/2.62  
% 6.30/2.62  
% 6.30/2.62  %Background operators:
% 6.30/2.62  
% 6.30/2.62  
% 6.30/2.62  %Foreground operators:
% 6.30/2.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.30/2.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.30/2.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.30/2.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.30/2.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.30/2.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.30/2.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.30/2.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.30/2.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.30/2.62  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 6.30/2.62  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 6.30/2.62  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.30/2.62  tff('#skF_3', type, '#skF_3': $i).
% 6.30/2.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.30/2.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.30/2.62  tff('#skF_4', type, '#skF_4': $i).
% 6.30/2.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.30/2.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.30/2.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.30/2.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.30/2.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.30/2.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.30/2.62  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.30/2.62  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.30/2.62  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.30/2.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.30/2.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.30/2.62  
% 6.30/2.64  tff(f_130, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 6.30/2.64  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 6.30/2.64  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.30/2.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.30/2.64  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.30/2.64  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.30/2.64  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 6.30/2.64  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.30/2.64  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.30/2.64  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.30/2.64  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.30/2.64  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.30/2.64  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 6.30/2.64  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 6.30/2.64  tff(c_58, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.30/2.64  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.30/2.64  tff(c_60, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.30/2.64  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.30/2.64  tff(c_1214, plain, (![A_147, B_148]: ('#skF_1'(A_147, B_148)!=B_148 | v3_tex_2(B_148, A_147) | ~v2_tex_2(B_148, A_147) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.30/2.64  tff(c_1225, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1214])).
% 6.30/2.64  tff(c_1234, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_1225])).
% 6.30/2.64  tff(c_1235, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_1234])).
% 6.30/2.64  tff(c_1618, plain, (![B_169, A_170]: (r1_tarski(B_169, '#skF_1'(A_170, B_169)) | v3_tex_2(B_169, A_170) | ~v2_tex_2(B_169, A_170) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.30/2.64  tff(c_1626, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1618])).
% 6.30/2.64  tff(c_1634, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_1626])).
% 6.30/2.64  tff(c_1635, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_1634])).
% 6.30/2.64  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.30/2.64  tff(c_1659, plain, (k4_xboole_0('#skF_4', '#skF_1'('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1635, c_10])).
% 6.30/2.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.30/2.64  tff(c_115, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.30/2.64  tff(c_131, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_115])).
% 6.30/2.64  tff(c_14, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.30/2.64  tff(c_18, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.30/2.64  tff(c_71, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 6.30/2.64  tff(c_314, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k3_subset_1(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.30/2.64  tff(c_320, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_subset_1(A_10, A_10))), inference(resolution, [status(thm)], [c_71, c_314])).
% 6.30/2.64  tff(c_329, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_320])).
% 6.30/2.64  tff(c_507, plain, (![A_96, B_97]: (k3_subset_1(A_96, k3_subset_1(A_96, B_97))=B_97 | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.30/2.64  tff(c_511, plain, (![A_10]: (k3_subset_1(A_10, k3_subset_1(A_10, A_10))=A_10)), inference(resolution, [status(thm)], [c_71, c_507])).
% 6.30/2.64  tff(c_518, plain, (![A_10]: (k3_subset_1(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_329, c_511])).
% 6.30/2.64  tff(c_24, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.30/2.64  tff(c_341, plain, (![A_77]: (k4_xboole_0(A_77, k1_xboole_0)=k3_subset_1(A_77, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_314])).
% 6.30/2.64  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.30/2.64  tff(c_347, plain, (![A_77]: (k4_xboole_0(A_77, k3_subset_1(A_77, k1_xboole_0))=k3_xboole_0(A_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_341, c_12])).
% 6.30/2.64  tff(c_534, plain, (![A_77]: (k4_xboole_0(A_77, A_77)=k3_xboole_0(A_77, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_347])).
% 6.30/2.64  tff(c_539, plain, (![A_77]: (k3_xboole_0(A_77, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_534])).
% 6.30/2.64  tff(c_1811, plain, (![A_176, B_177]: (m1_subset_1('#skF_1'(A_176, B_177), k1_zfmisc_1(u1_struct_0(A_176))) | v3_tex_2(B_177, A_176) | ~v2_tex_2(B_177, A_176) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.30/2.64  tff(c_28, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.30/2.64  tff(c_3307, plain, (![A_225, B_226]: (r1_tarski('#skF_1'(A_225, B_226), u1_struct_0(A_225)) | v3_tex_2(B_226, A_225) | ~v2_tex_2(B_226, A_225) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_225))) | ~l1_pre_topc(A_225))), inference(resolution, [status(thm)], [c_1811, c_28])).
% 6.30/2.64  tff(c_3736, plain, (![A_240, B_241]: (k4_xboole_0('#skF_1'(A_240, B_241), u1_struct_0(A_240))=k1_xboole_0 | v3_tex_2(B_241, A_240) | ~v2_tex_2(B_241, A_240) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240))), inference(resolution, [status(thm)], [c_3307, c_10])).
% 6.30/2.64  tff(c_3748, plain, (k4_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))=k1_xboole_0 | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_3736])).
% 6.30/2.64  tff(c_3758, plain, (k4_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))=k1_xboole_0 | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_3748])).
% 6.30/2.64  tff(c_3759, plain, (k4_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_3758])).
% 6.30/2.64  tff(c_1541, plain, (![A_160, B_161]: (v2_tex_2('#skF_1'(A_160, B_161), A_160) | v3_tex_2(B_161, A_160) | ~v2_tex_2(B_161, A_160) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.30/2.64  tff(c_1549, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1541])).
% 6.30/2.64  tff(c_1557, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_1549])).
% 6.30/2.64  tff(c_1558, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_1557])).
% 6.30/2.64  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.30/2.64  tff(c_30, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.30/2.64  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.30/2.64  tff(c_68, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.30/2.64  tff(c_521, plain, (![A_98, B_99, C_100]: (k9_subset_1(A_98, B_99, C_100)=k3_xboole_0(B_99, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.30/2.64  tff(c_531, plain, (![A_10, B_99]: (k9_subset_1(A_10, B_99, A_10)=k3_xboole_0(B_99, A_10))), inference(resolution, [status(thm)], [c_71, c_521])).
% 6.30/2.64  tff(c_62, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.30/2.64  tff(c_819, plain, (![A_121, B_122]: (k2_pre_topc(A_121, B_122)=u1_struct_0(A_121) | ~v1_tops_1(B_122, A_121) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.30/2.64  tff(c_830, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_819])).
% 6.30/2.64  tff(c_839, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_830])).
% 6.30/2.64  tff(c_2782, plain, (![A_214, B_215, C_216]: (k9_subset_1(u1_struct_0(A_214), B_215, k2_pre_topc(A_214, C_216))=C_216 | ~r1_tarski(C_216, B_215) | ~m1_subset_1(C_216, k1_zfmisc_1(u1_struct_0(A_214))) | ~v2_tex_2(B_215, A_214) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214) | v2_struct_0(A_214))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.30/2.64  tff(c_2794, plain, (![B_215]: (k9_subset_1(u1_struct_0('#skF_3'), B_215, k2_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', B_215) | ~v2_tex_2(B_215, '#skF_3') | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_64, c_2782])).
% 6.30/2.64  tff(c_2804, plain, (![B_215]: (k3_xboole_0(B_215, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_215) | ~v2_tex_2(B_215, '#skF_3') | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_531, c_839, c_2794])).
% 6.30/2.64  tff(c_2809, plain, (![B_217]: (k3_xboole_0(B_217, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_217) | ~v2_tex_2(B_217, '#skF_3') | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_2804])).
% 6.30/2.64  tff(c_2890, plain, (![A_219]: (k3_xboole_0(A_219, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', A_219) | ~v2_tex_2(A_219, '#skF_3') | ~r1_tarski(A_219, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_30, c_2809])).
% 6.30/2.64  tff(c_2924, plain, (![A_3]: (k3_xboole_0(A_3, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', A_3) | ~v2_tex_2(A_3, '#skF_3') | k4_xboole_0(A_3, u1_struct_0('#skF_3'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_2890])).
% 6.30/2.64  tff(c_3778, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3759, c_2924])).
% 6.30/2.64  tff(c_3824, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1635, c_3778])).
% 6.30/2.64  tff(c_206, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.30/2.64  tff(c_209, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k3_xboole_0(A_69, k4_xboole_0(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_206, c_12])).
% 6.30/2.64  tff(c_158, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.30/2.64  tff(c_464, plain, (![B_89, A_90]: (B_89=A_90 | ~r1_tarski(B_89, A_90) | k4_xboole_0(A_90, B_89)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_158])).
% 6.30/2.64  tff(c_920, plain, (![B_127, A_128]: (B_127=A_128 | k4_xboole_0(B_127, A_128)!=k1_xboole_0 | k4_xboole_0(A_128, B_127)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_464])).
% 6.30/2.64  tff(c_922, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=A_69 | k3_xboole_0(A_69, k4_xboole_0(A_69, B_70))!=k1_xboole_0 | k4_xboole_0(k3_xboole_0(A_69, B_70), A_69)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_209, c_920])).
% 6.30/2.64  tff(c_3858, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), k4_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3')))!=k1_xboole_0 | k4_xboole_0('#skF_4', '#skF_1'('#skF_3', '#skF_4'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3824, c_922])).
% 6.30/2.64  tff(c_3871, plain, ('#skF_1'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1659, c_539, c_3759, c_3824, c_3858])).
% 6.30/2.64  tff(c_3873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1235, c_3871])).
% 6.30/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.64  
% 6.30/2.64  Inference rules
% 6.30/2.64  ----------------------
% 6.30/2.64  #Ref     : 0
% 6.30/2.64  #Sup     : 901
% 6.30/2.64  #Fact    : 0
% 6.30/2.64  #Define  : 0
% 6.30/2.64  #Split   : 8
% 6.30/2.64  #Chain   : 0
% 6.30/2.64  #Close   : 0
% 6.30/2.64  
% 6.30/2.64  Ordering : KBO
% 6.30/2.64  
% 6.30/2.64  Simplification rules
% 6.30/2.64  ----------------------
% 6.30/2.64  #Subsume      : 85
% 6.30/2.64  #Demod        : 968
% 6.30/2.64  #Tautology    : 357
% 6.30/2.64  #SimpNegUnit  : 34
% 6.30/2.64  #BackRed      : 11
% 6.30/2.64  
% 6.30/2.64  #Partial instantiations: 0
% 6.30/2.64  #Strategies tried      : 1
% 6.30/2.64  
% 6.30/2.64  Timing (in seconds)
% 6.30/2.64  ----------------------
% 6.30/2.64  Preprocessing        : 0.55
% 6.30/2.64  Parsing              : 0.28
% 6.30/2.64  CNF conversion       : 0.04
% 6.30/2.64  Main loop            : 1.27
% 6.30/2.64  Inferencing          : 0.40
% 6.30/2.64  Reduction            : 0.48
% 6.30/2.64  Demodulation         : 0.36
% 6.30/2.64  BG Simplification    : 0.05
% 6.30/2.64  Subsumption          : 0.25
% 6.30/2.64  Abstraction          : 0.08
% 6.30/2.64  MUC search           : 0.00
% 6.30/2.64  Cooper               : 0.00
% 6.30/2.64  Total                : 1.86
% 6.30/2.64  Index Insertion      : 0.00
% 6.30/2.64  Index Deletion       : 0.00
% 6.30/2.64  Index Matching       : 0.00
% 6.30/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
