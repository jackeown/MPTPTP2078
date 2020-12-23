%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:08 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  146 (1892 expanded)
%              Number of leaves         :   43 ( 644 expanded)
%              Depth                    :   20
%              Number of atoms          :  276 (4325 expanded)
%              Number of equality atoms :   70 (1030 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tops_1)).

tff(f_32,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_30,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_28,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_310,plain,(
    ! [B_74,A_75] :
      ( v3_pre_topc(B_74,A_75)
      | ~ v1_xboole_0(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_318,plain,(
    ! [A_75] :
      ( v3_pre_topc(k1_xboole_0,A_75)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_20,c_310])).

tff(c_329,plain,(
    ! [A_75] :
      ( v3_pre_topc(k1_xboole_0,A_75)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_318])).

tff(c_270,plain,(
    ! [B_67,A_68] :
      ( v3_tops_1(B_67,A_68)
      | ~ v1_xboole_0(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_278,plain,(
    ! [A_68] :
      ( v3_tops_1(k1_xboole_0,A_68)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_20,c_270])).

tff(c_289,plain,(
    ! [A_68] :
      ( v3_tops_1(k1_xboole_0,A_68)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_278])).

tff(c_8,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_92,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_101,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_92])).

tff(c_104,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_101])).

tff(c_170,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = k3_subset_1(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_176,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = k3_subset_1(A_13,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_170])).

tff(c_185,plain,(
    ! [A_13] : k3_subset_1(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_176])).

tff(c_669,plain,(
    ! [A_109,B_110] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_109),B_110),A_109)
      | ~ v3_pre_topc(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_684,plain,(
    ! [A_109] :
      ( v4_pre_topc(u1_struct_0(A_109),A_109)
      | ~ v3_pre_topc(k1_xboole_0,A_109)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_669])).

tff(c_711,plain,(
    ! [A_112] :
      ( v4_pre_topc(u1_struct_0(A_112),A_112)
      | ~ v3_pre_topc(k1_xboole_0,A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_684])).

tff(c_10,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_55,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_335,plain,(
    ! [A_77,B_78] :
      ( k2_pre_topc(A_77,B_78) = B_78
      | ~ v4_pre_topc(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_356,plain,(
    ! [A_77] :
      ( k2_pre_topc(A_77,u1_struct_0(A_77)) = u1_struct_0(A_77)
      | ~ v4_pre_topc(u1_struct_0(A_77),A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_55,c_335])).

tff(c_721,plain,(
    ! [A_114] :
      ( k2_pre_topc(A_114,u1_struct_0(A_114)) = u1_struct_0(A_114)
      | ~ v3_pre_topc(k1_xboole_0,A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_711,c_356])).

tff(c_418,plain,(
    ! [A_89,B_90] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_89),B_90),A_89)
      | ~ v3_tops_1(B_90,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_426,plain,(
    ! [A_89] :
      ( v1_tops_1(u1_struct_0(A_89),A_89)
      | ~ v3_tops_1(k1_xboole_0,A_89)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_418])).

tff(c_442,plain,(
    ! [A_92] :
      ( v1_tops_1(u1_struct_0(A_92),A_92)
      | ~ v3_tops_1(k1_xboole_0,A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_426])).

tff(c_385,plain,(
    ! [A_85,B_86] :
      ( k2_pre_topc(A_85,B_86) = k2_struct_0(A_85)
      | ~ v1_tops_1(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_407,plain,(
    ! [A_85] :
      ( k2_pre_topc(A_85,u1_struct_0(A_85)) = k2_struct_0(A_85)
      | ~ v1_tops_1(u1_struct_0(A_85),A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_55,c_385])).

tff(c_446,plain,(
    ! [A_92] :
      ( k2_pre_topc(A_92,u1_struct_0(A_92)) = k2_struct_0(A_92)
      | ~ v3_tops_1(k1_xboole_0,A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_442,c_407])).

tff(c_736,plain,(
    ! [A_115] :
      ( u1_struct_0(A_115) = k2_struct_0(A_115)
      | ~ v3_tops_1(k1_xboole_0,A_115)
      | ~ l1_pre_topc(A_115)
      | ~ v3_pre_topc(k1_xboole_0,A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_446])).

tff(c_769,plain,(
    ! [A_118] :
      ( u1_struct_0(A_118) = k2_struct_0(A_118)
      | ~ v3_pre_topc(k1_xboole_0,A_118)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_289,c_736])).

tff(c_774,plain,(
    ! [A_119] :
      ( u1_struct_0(A_119) = k2_struct_0(A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_329,c_769])).

tff(c_777,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_774])).

tff(c_780,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_777])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_792,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_50])).

tff(c_48,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    ! [A_31,B_33] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_31),B_33),A_31)
      | ~ v3_pre_topc(B_33,A_31)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_811,plain,(
    ! [B_33] :
      ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_33),'#skF_1')
      | ~ v3_pre_topc(B_33,'#skF_1')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_40])).

tff(c_1401,plain,(
    ! [B_142] :
      ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_142),'#skF_1')
      | ~ v3_pre_topc(B_142,'#skF_1')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_780,c_811])).

tff(c_46,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    ! [A_34,B_36] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_34),B_36),A_34)
      | ~ v3_tops_1(B_36,A_34)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_359,plain,(
    ! [B_80,A_81] :
      ( v1_tops_1(B_80,A_81)
      | k2_pre_topc(A_81,B_80) != k2_struct_0(A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_370,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_359])).

tff(c_379,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_370])).

tff(c_381,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_396,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_385])).

tff(c_405,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_396])).

tff(c_406,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_405])).

tff(c_115,plain,(
    ! [A_50,B_51] :
      ( k3_subset_1(A_50,k3_subset_1(A_50,B_51)) = B_51
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_126,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_50,c_115])).

tff(c_429,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_418])).

tff(c_435,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_429])).

tff(c_436,plain,
    ( ~ v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_435])).

tff(c_537,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_540,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_16,c_537])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_540])).

tff(c_546,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_34,plain,(
    ! [B_30,A_28] :
      ( v1_tops_1(B_30,A_28)
      | k2_pre_topc(A_28,B_30) != k2_struct_0(A_28)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_552,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_546,c_34])).

tff(c_574,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_552])).

tff(c_658,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_36,plain,(
    ! [A_28,B_30] :
      ( k2_pre_topc(A_28,B_30) = k2_struct_0(A_28)
      | ~ v1_tops_1(B_30,A_28)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_549,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_546,c_36])).

tff(c_571,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_549])).

tff(c_659,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_571])).

tff(c_662,plain,
    ( ~ v3_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_659])).

tff(c_666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_662])).

tff(c_668,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_781,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_668])).

tff(c_787,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_780,c_546])).

tff(c_26,plain,(
    ! [B_21,A_19] :
      ( v4_pre_topc(B_21,A_19)
      | k2_pre_topc(A_19,B_21) != B_21
      | ~ v2_pre_topc(A_19)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_817,plain,(
    ! [B_21] :
      ( v4_pre_topc(B_21,'#skF_1')
      | k2_pre_topc('#skF_1',B_21) != B_21
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_26])).

tff(c_1237,plain,(
    ! [B_134] :
      ( v4_pre_topc(B_134,'#skF_1')
      | k2_pre_topc('#skF_1',B_134) != B_134
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_817])).

tff(c_1240,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_787,c_1237])).

tff(c_1257,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_1240])).

tff(c_1295,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1257])).

tff(c_28,plain,(
    ! [A_19,B_21] :
      ( k2_pre_topc(A_19,B_21) = B_21
      | ~ v4_pre_topc(B_21,A_19)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_862,plain,(
    ! [B_21] :
      ( k2_pre_topc('#skF_1',B_21) = B_21
      | ~ v4_pre_topc(B_21,'#skF_1')
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_28])).

tff(c_1266,plain,(
    ! [B_135] :
      ( k2_pre_topc('#skF_1',B_135) = B_135
      | ~ v4_pre_topc(B_135,'#skF_1')
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_862])).

tff(c_1269,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_787,c_1266])).

tff(c_1286,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_1269])).

tff(c_1296,plain,(
    ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1295,c_1286])).

tff(c_1404,plain,
    ( ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1401,c_1296])).

tff(c_1423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_48,c_1404])).

tff(c_1425,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1257])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k3_subset_1(A_6,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_566,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_546,c_12])).

tff(c_587,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_566])).

tff(c_785,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_780,c_587])).

tff(c_1448,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_785])).

tff(c_125,plain,(
    ! [A_13] : k3_subset_1(A_13,k3_subset_1(A_13,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_115])).

tff(c_188,plain,(
    ! [A_13] : k3_subset_1(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_125])).

tff(c_187,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_subset_1(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_55,c_170])).

tff(c_232,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_187])).

tff(c_1481,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1448,c_232])).

tff(c_1487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:23:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.60  
% 3.57/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.60  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.57/1.60  
% 3.57/1.60  %Foreground sorts:
% 3.57/1.60  
% 3.57/1.60  
% 3.57/1.60  %Background operators:
% 3.57/1.60  
% 3.57/1.60  
% 3.57/1.60  %Foreground operators:
% 3.57/1.60  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.57/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.57/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.57/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.57/1.60  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.57/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.57/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.57/1.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.57/1.60  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.57/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.60  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.57/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.57/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.57/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.57/1.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.57/1.60  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.57/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.57/1.60  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.57/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.57/1.60  
% 3.86/1.63  tff(f_136, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 3.86/1.63  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.86/1.63  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.86/1.63  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 3.86/1.63  tff(f_95, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_tops_1)).
% 3.86/1.63  tff(f_32, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.86/1.63  tff(f_30, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.86/1.63  tff(f_28, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.86/1.63  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.86/1.63  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 3.86/1.63  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.86/1.63  tff(f_40, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.86/1.63  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.86/1.63  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 3.86/1.63  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.86/1.63  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.86/1.63  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.86/1.63  tff(c_44, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.86/1.63  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.86/1.63  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.86/1.63  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.86/1.63  tff(c_20, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.86/1.63  tff(c_310, plain, (![B_74, A_75]: (v3_pre_topc(B_74, A_75) | ~v1_xboole_0(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.86/1.63  tff(c_318, plain, (![A_75]: (v3_pre_topc(k1_xboole_0, A_75) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(resolution, [status(thm)], [c_20, c_310])).
% 3.86/1.63  tff(c_329, plain, (![A_75]: (v3_pre_topc(k1_xboole_0, A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_318])).
% 3.86/1.63  tff(c_270, plain, (![B_67, A_68]: (v3_tops_1(B_67, A_68) | ~v1_xboole_0(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.86/1.63  tff(c_278, plain, (![A_68]: (v3_tops_1(k1_xboole_0, A_68) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(resolution, [status(thm)], [c_20, c_270])).
% 3.86/1.63  tff(c_289, plain, (![A_68]: (v3_tops_1(k1_xboole_0, A_68) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_278])).
% 3.86/1.63  tff(c_8, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.86/1.63  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.86/1.63  tff(c_92, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.86/1.63  tff(c_101, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_92])).
% 3.86/1.63  tff(c_104, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_101])).
% 3.86/1.63  tff(c_170, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=k3_subset_1(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.86/1.63  tff(c_176, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=k3_subset_1(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_170])).
% 3.86/1.63  tff(c_185, plain, (![A_13]: (k3_subset_1(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_104, c_176])).
% 3.86/1.63  tff(c_669, plain, (![A_109, B_110]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_109), B_110), A_109) | ~v3_pre_topc(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.86/1.63  tff(c_684, plain, (![A_109]: (v4_pre_topc(u1_struct_0(A_109), A_109) | ~v3_pre_topc(k1_xboole_0, A_109) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(superposition, [status(thm), theory('equality')], [c_185, c_669])).
% 3.86/1.63  tff(c_711, plain, (![A_112]: (v4_pre_topc(u1_struct_0(A_112), A_112) | ~v3_pre_topc(k1_xboole_0, A_112) | ~l1_pre_topc(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_684])).
% 3.86/1.63  tff(c_10, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.86/1.63  tff(c_14, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.86/1.63  tff(c_55, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 3.86/1.63  tff(c_335, plain, (![A_77, B_78]: (k2_pre_topc(A_77, B_78)=B_78 | ~v4_pre_topc(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.86/1.63  tff(c_356, plain, (![A_77]: (k2_pre_topc(A_77, u1_struct_0(A_77))=u1_struct_0(A_77) | ~v4_pre_topc(u1_struct_0(A_77), A_77) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_55, c_335])).
% 3.86/1.63  tff(c_721, plain, (![A_114]: (k2_pre_topc(A_114, u1_struct_0(A_114))=u1_struct_0(A_114) | ~v3_pre_topc(k1_xboole_0, A_114) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_711, c_356])).
% 3.86/1.63  tff(c_418, plain, (![A_89, B_90]: (v1_tops_1(k3_subset_1(u1_struct_0(A_89), B_90), A_89) | ~v3_tops_1(B_90, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.86/1.63  tff(c_426, plain, (![A_89]: (v1_tops_1(u1_struct_0(A_89), A_89) | ~v3_tops_1(k1_xboole_0, A_89) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(superposition, [status(thm), theory('equality')], [c_185, c_418])).
% 3.86/1.63  tff(c_442, plain, (![A_92]: (v1_tops_1(u1_struct_0(A_92), A_92) | ~v3_tops_1(k1_xboole_0, A_92) | ~l1_pre_topc(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_426])).
% 3.86/1.63  tff(c_385, plain, (![A_85, B_86]: (k2_pre_topc(A_85, B_86)=k2_struct_0(A_85) | ~v1_tops_1(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.86/1.63  tff(c_407, plain, (![A_85]: (k2_pre_topc(A_85, u1_struct_0(A_85))=k2_struct_0(A_85) | ~v1_tops_1(u1_struct_0(A_85), A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_55, c_385])).
% 3.86/1.63  tff(c_446, plain, (![A_92]: (k2_pre_topc(A_92, u1_struct_0(A_92))=k2_struct_0(A_92) | ~v3_tops_1(k1_xboole_0, A_92) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_442, c_407])).
% 3.86/1.63  tff(c_736, plain, (![A_115]: (u1_struct_0(A_115)=k2_struct_0(A_115) | ~v3_tops_1(k1_xboole_0, A_115) | ~l1_pre_topc(A_115) | ~v3_pre_topc(k1_xboole_0, A_115) | ~l1_pre_topc(A_115))), inference(superposition, [status(thm), theory('equality')], [c_721, c_446])).
% 3.86/1.63  tff(c_769, plain, (![A_118]: (u1_struct_0(A_118)=k2_struct_0(A_118) | ~v3_pre_topc(k1_xboole_0, A_118) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118))), inference(resolution, [status(thm)], [c_289, c_736])).
% 3.86/1.63  tff(c_774, plain, (![A_119]: (u1_struct_0(A_119)=k2_struct_0(A_119) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119))), inference(resolution, [status(thm)], [c_329, c_769])).
% 3.86/1.63  tff(c_777, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_774])).
% 3.86/1.63  tff(c_780, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_777])).
% 3.86/1.63  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.86/1.63  tff(c_792, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_780, c_50])).
% 3.86/1.63  tff(c_48, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.86/1.63  tff(c_40, plain, (![A_31, B_33]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_31), B_33), A_31) | ~v3_pre_topc(B_33, A_31) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.86/1.63  tff(c_811, plain, (![B_33]: (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_33), '#skF_1') | ~v3_pre_topc(B_33, '#skF_1') | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_780, c_40])).
% 3.86/1.63  tff(c_1401, plain, (![B_142]: (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_142), '#skF_1') | ~v3_pre_topc(B_142, '#skF_1') | ~m1_subset_1(B_142, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_780, c_811])).
% 3.86/1.63  tff(c_46, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.86/1.63  tff(c_42, plain, (![A_34, B_36]: (v1_tops_1(k3_subset_1(u1_struct_0(A_34), B_36), A_34) | ~v3_tops_1(B_36, A_34) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.86/1.63  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(k3_subset_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.86/1.63  tff(c_359, plain, (![B_80, A_81]: (v1_tops_1(B_80, A_81) | k2_pre_topc(A_81, B_80)!=k2_struct_0(A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.86/1.63  tff(c_370, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_359])).
% 3.86/1.63  tff(c_379, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_370])).
% 3.86/1.63  tff(c_381, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_379])).
% 3.86/1.63  tff(c_396, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_385])).
% 3.86/1.63  tff(c_405, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_396])).
% 3.86/1.63  tff(c_406, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_381, c_405])).
% 3.86/1.63  tff(c_115, plain, (![A_50, B_51]: (k3_subset_1(A_50, k3_subset_1(A_50, B_51))=B_51 | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.86/1.63  tff(c_126, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_50, c_115])).
% 3.86/1.63  tff(c_429, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_126, c_418])).
% 3.86/1.63  tff(c_435, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_429])).
% 3.86/1.63  tff(c_436, plain, (~v3_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_406, c_435])).
% 3.86/1.63  tff(c_537, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_436])).
% 3.86/1.63  tff(c_540, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_537])).
% 3.86/1.63  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_540])).
% 3.86/1.63  tff(c_546, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_436])).
% 3.86/1.63  tff(c_34, plain, (![B_30, A_28]: (v1_tops_1(B_30, A_28) | k2_pre_topc(A_28, B_30)!=k2_struct_0(A_28) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.86/1.63  tff(c_552, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_546, c_34])).
% 3.86/1.63  tff(c_574, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_552])).
% 3.86/1.63  tff(c_658, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_574])).
% 3.86/1.63  tff(c_36, plain, (![A_28, B_30]: (k2_pre_topc(A_28, B_30)=k2_struct_0(A_28) | ~v1_tops_1(B_30, A_28) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.86/1.63  tff(c_549, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_546, c_36])).
% 3.86/1.63  tff(c_571, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_549])).
% 3.86/1.63  tff(c_659, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_658, c_571])).
% 3.86/1.63  tff(c_662, plain, (~v3_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_659])).
% 3.86/1.63  tff(c_666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_662])).
% 3.86/1.63  tff(c_668, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_574])).
% 3.86/1.63  tff(c_781, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_780, c_668])).
% 3.86/1.63  tff(c_787, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_780, c_780, c_546])).
% 3.86/1.63  tff(c_26, plain, (![B_21, A_19]: (v4_pre_topc(B_21, A_19) | k2_pre_topc(A_19, B_21)!=B_21 | ~v2_pre_topc(A_19) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.86/1.63  tff(c_817, plain, (![B_21]: (v4_pre_topc(B_21, '#skF_1') | k2_pre_topc('#skF_1', B_21)!=B_21 | ~v2_pre_topc('#skF_1') | ~m1_subset_1(B_21, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_780, c_26])).
% 3.86/1.63  tff(c_1237, plain, (![B_134]: (v4_pre_topc(B_134, '#skF_1') | k2_pre_topc('#skF_1', B_134)!=B_134 | ~m1_subset_1(B_134, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_817])).
% 3.86/1.63  tff(c_1240, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_787, c_1237])).
% 3.86/1.63  tff(c_1257, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_781, c_1240])).
% 3.86/1.63  tff(c_1295, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1257])).
% 3.86/1.63  tff(c_28, plain, (![A_19, B_21]: (k2_pre_topc(A_19, B_21)=B_21 | ~v4_pre_topc(B_21, A_19) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.86/1.63  tff(c_862, plain, (![B_21]: (k2_pre_topc('#skF_1', B_21)=B_21 | ~v4_pre_topc(B_21, '#skF_1') | ~m1_subset_1(B_21, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_780, c_28])).
% 3.86/1.63  tff(c_1266, plain, (![B_135]: (k2_pre_topc('#skF_1', B_135)=B_135 | ~v4_pre_topc(B_135, '#skF_1') | ~m1_subset_1(B_135, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_862])).
% 3.86/1.63  tff(c_1269, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_787, c_1266])).
% 3.86/1.63  tff(c_1286, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_781, c_1269])).
% 3.86/1.63  tff(c_1296, plain, (~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1295, c_1286])).
% 3.86/1.63  tff(c_1404, plain, (~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1401, c_1296])).
% 3.86/1.63  tff(c_1423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_792, c_48, c_1404])).
% 3.86/1.63  tff(c_1425, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1257])).
% 3.86/1.63  tff(c_12, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k3_subset_1(A_6, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.86/1.63  tff(c_566, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_546, c_12])).
% 3.86/1.63  tff(c_587, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_566])).
% 3.86/1.63  tff(c_785, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_780, c_780, c_587])).
% 3.86/1.63  tff(c_1448, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1425, c_785])).
% 3.86/1.63  tff(c_125, plain, (![A_13]: (k3_subset_1(A_13, k3_subset_1(A_13, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_115])).
% 3.86/1.63  tff(c_188, plain, (![A_13]: (k3_subset_1(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_185, c_125])).
% 3.86/1.63  tff(c_187, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_subset_1(A_8, A_8))), inference(resolution, [status(thm)], [c_55, c_170])).
% 3.86/1.63  tff(c_232, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_188, c_187])).
% 3.86/1.63  tff(c_1481, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1448, c_232])).
% 3.86/1.63  tff(c_1487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1481])).
% 3.86/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.63  
% 3.86/1.63  Inference rules
% 3.86/1.63  ----------------------
% 3.86/1.63  #Ref     : 0
% 3.86/1.63  #Sup     : 283
% 3.86/1.63  #Fact    : 0
% 3.86/1.63  #Define  : 0
% 3.86/1.63  #Split   : 11
% 3.86/1.63  #Chain   : 0
% 3.86/1.63  #Close   : 0
% 3.86/1.63  
% 3.86/1.63  Ordering : KBO
% 3.86/1.63  
% 3.86/1.63  Simplification rules
% 3.86/1.63  ----------------------
% 3.86/1.63  #Subsume      : 49
% 3.86/1.63  #Demod        : 295
% 3.86/1.63  #Tautology    : 122
% 3.86/1.63  #SimpNegUnit  : 23
% 3.86/1.63  #BackRed      : 25
% 3.86/1.63  
% 3.86/1.63  #Partial instantiations: 0
% 3.86/1.63  #Strategies tried      : 1
% 3.86/1.63  
% 3.86/1.63  Timing (in seconds)
% 3.86/1.63  ----------------------
% 3.86/1.63  Preprocessing        : 0.33
% 3.86/1.63  Parsing              : 0.18
% 3.86/1.63  CNF conversion       : 0.02
% 3.86/1.63  Main loop            : 0.49
% 3.86/1.63  Inferencing          : 0.17
% 3.86/1.63  Reduction            : 0.17
% 3.86/1.63  Demodulation         : 0.12
% 3.86/1.63  BG Simplification    : 0.02
% 3.86/1.63  Subsumption          : 0.08
% 3.86/1.63  Abstraction          : 0.02
% 3.86/1.63  MUC search           : 0.00
% 3.86/1.63  Cooper               : 0.00
% 3.86/1.63  Total                : 0.87
% 3.86/1.63  Index Insertion      : 0.00
% 3.86/1.63  Index Deletion       : 0.00
% 3.86/1.63  Index Matching       : 0.00
% 3.86/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
