%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1311+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:46 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 220 expanded)
%              Number of leaves         :   41 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 446 expanded)
%              Number of equality atoms :   28 (  85 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_2 > v1_tops_2 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v2_tops_2(B,A)
             => v4_pre_topc(k6_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k6_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_118,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
           => v3_pre_topc(k5_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tops_2)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_116,plain,(
    ! [A_51,B_52] :
      ( k6_setfam_1(A_51,B_52) = k1_setfam_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_120,plain,(
    k6_setfam_1(u1_struct_0('#skF_5'),'#skF_6') = k1_setfam_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_116])).

tff(c_52,plain,(
    ~ v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_5'),'#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_121,plain,(
    ~ v4_pre_topc(k1_setfam_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_52])).

tff(c_58,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_126,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k6_setfam_1(A_53,B_54),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_133,plain,
    ( m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_126])).

tff(c_136,plain,(
    m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_133])).

tff(c_60,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_54,plain,(
    v2_tops_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_217,plain,(
    ! [A_79,B_80] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_79),B_80),A_79)
      | ~ v2_tops_2(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79))))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_225,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6'),'#skF_5')
    | ~ v2_tops_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_217])).

tff(c_230,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_225])).

tff(c_236,plain,(
    ! [A_81,B_82] :
      ( k5_setfam_1(A_81,k7_setfam_1(A_81,B_82)) = k3_subset_1(A_81,k6_setfam_1(A_81,B_82))
      | k1_xboole_0 = B_82
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_243,plain,
    ( k5_setfam_1(u1_struct_0('#skF_5'),k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6')) = k3_subset_1(u1_struct_0('#skF_5'),k6_setfam_1(u1_struct_0('#skF_5'),'#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_56,c_236])).

tff(c_247,plain,
    ( k5_setfam_1(u1_struct_0('#skF_5'),k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6')) = k3_subset_1(u1_struct_0('#skF_5'),k1_setfam_1('#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_243])).

tff(c_248,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_32,plain,(
    ! [A_28] :
      ( l1_struct_0(A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_68,plain,(
    ! [A_47] :
      ( v1_xboole_0(k1_struct_0(A_47))
      | ~ l1_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_73,plain,(
    ! [A_48] :
      ( k1_struct_0(A_48) = k1_xboole_0
      | ~ l1_struct_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_68,c_50])).

tff(c_78,plain,(
    ! [A_49] :
      ( k1_struct_0(A_49) = k1_xboole_0
      | ~ l1_pre_topc(A_49) ) ),
    inference(resolution,[status(thm)],[c_32,c_73])).

tff(c_82,plain,(
    k1_struct_0('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_78])).

tff(c_34,plain,(
    ! [A_29] :
      ( v1_xboole_0(k1_struct_0(A_29))
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_86,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_34])).

tff(c_90,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_93,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_90])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_93])).

tff(c_98,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_257,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_98])).

tff(c_24,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_262,plain,(
    k1_setfam_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_248,c_24])).

tff(c_158,plain,(
    ! [B_64,A_65] :
      ( v4_pre_topc(B_64,A_65)
      | ~ v1_xboole_0(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_161,plain,
    ( v4_pre_topc(k1_setfam_1('#skF_6'),'#skF_5')
    | ~ v1_xboole_0(k1_setfam_1('#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_136,c_158])).

tff(c_174,plain,
    ( v4_pre_topc(k1_setfam_1('#skF_6'),'#skF_5')
    | ~ v1_xboole_0(k1_setfam_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_161])).

tff(c_175,plain,(
    ~ v1_xboole_0(k1_setfam_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_174])).

tff(c_267,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_175])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_267])).

tff(c_274,plain,(
    k5_setfam_1(u1_struct_0('#skF_5'),k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6')) = k3_subset_1(u1_struct_0('#skF_5'),k1_setfam_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k7_setfam_1(A_26,B_27),k1_zfmisc_1(k1_zfmisc_1(A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_137,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k7_setfam_1(A_55,B_56),k1_zfmisc_1(k1_zfmisc_1(A_55)))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    ! [A_30,B_31] :
      ( k6_setfam_1(A_30,B_31) = k1_setfam_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_187,plain,(
    ! [A_67,B_68] :
      ( k6_setfam_1(A_67,k7_setfam_1(A_67,B_68)) = k1_setfam_1(k7_setfam_1(A_67,B_68))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(resolution,[status(thm)],[c_137,c_36])).

tff(c_197,plain,(
    k6_setfam_1(u1_struct_0('#skF_5'),k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6')) = k1_setfam_1(k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_187])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k6_setfam_1(A_24,B_25),k1_zfmisc_1(A_24))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_201,plain,
    ( m1_subset_1(k1_setfam_1(k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_28])).

tff(c_299,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_302,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_30,c_299])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_302])).

tff(c_308,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_431,plain,(
    ! [A_103,B_104] :
      ( v3_pre_topc(k5_setfam_1(u1_struct_0(A_103),B_104),A_103)
      | ~ v1_tops_2(B_104,A_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_103))))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_433,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_5'),k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6')),'#skF_5')
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_5'),'#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_308,c_431])).

tff(c_444,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_5'),k1_setfam_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_230,c_274,c_433])).

tff(c_46,plain,(
    ! [B_42,A_40] :
      ( v4_pre_topc(B_42,A_40)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_40),B_42),A_40)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_453,plain,
    ( v4_pre_topc(k1_setfam_1('#skF_6'),'#skF_5')
    | ~ m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_444,c_46])).

tff(c_456,plain,(
    v4_pre_topc(k1_setfam_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_136,c_453])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_456])).

%------------------------------------------------------------------------------
