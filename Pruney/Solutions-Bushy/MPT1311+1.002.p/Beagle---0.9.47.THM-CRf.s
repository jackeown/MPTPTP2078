%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1311+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:46 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 199 expanded)
%              Number of leaves         :   42 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  142 ( 396 expanded)
%              Number of equality atoms :   27 (  79 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_2 > v1_tops_2 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v2_tops_2(B,A)
             => v4_pre_topc(k6_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k6_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_setfam_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_64,axiom,(
    ? [A] : l1_struct_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l1_struct_0)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
           => v3_pre_topc(k5_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tops_2)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_89,plain,(
    ! [A_46,B_47] :
      ( k6_setfam_1(A_46,B_47) = k1_setfam_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_93,plain,(
    k6_setfam_1(u1_struct_0('#skF_6'),'#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_89])).

tff(c_50,plain,(
    ~ v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_94,plain,(
    ~ v4_pre_topc(k1_setfam_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_50])).

tff(c_56,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_99,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k6_setfam_1(A_48,B_49),k1_zfmisc_1(A_48))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,
    ( m1_subset_1(k1_setfam_1('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_99])).

tff(c_109,plain,(
    m1_subset_1(k1_setfam_1('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_106])).

tff(c_58,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_52,plain,(
    v2_tops_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_198,plain,(
    ! [A_71,B_72] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_71),B_72),A_71)
      | ~ v2_tops_2(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71))))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_208,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6')
    | ~ v2_tops_2('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_198])).

tff(c_216,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_208])).

tff(c_225,plain,(
    ! [A_73,B_74] :
      ( k5_setfam_1(A_73,k7_setfam_1(A_73,B_74)) = k3_subset_1(A_73,k6_setfam_1(A_73,B_74))
      | k1_xboole_0 = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_234,plain,
    ( k5_setfam_1(u1_struct_0('#skF_6'),k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7')) = k3_subset_1(u1_struct_0('#skF_6'),k6_setfam_1(u1_struct_0('#skF_6'),'#skF_7'))
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_54,c_225])).

tff(c_240,plain,
    ( k5_setfam_1(u1_struct_0('#skF_6'),k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7')) = k3_subset_1(u1_struct_0('#skF_6'),k1_setfam_1('#skF_7'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_234])).

tff(c_241,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_30,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_65,plain,(
    ! [A_44] :
      ( v1_xboole_0(k1_struct_0(A_44))
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_70,plain,(
    ! [A_45] :
      ( k1_struct_0(A_45) = k1_xboole_0
      | ~ l1_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_65,c_48])).

tff(c_74,plain,(
    k1_struct_0('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_32,plain,(
    ! [A_27] :
      ( v1_xboole_0(k1_struct_0(A_27))
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_78,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_32])).

tff(c_82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_78])).

tff(c_248,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_82])).

tff(c_24,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_252,plain,(
    k1_setfam_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_241,c_24])).

tff(c_131,plain,(
    ! [B_59,A_60] :
      ( v4_pre_topc(B_59,A_60)
      | ~ v1_xboole_0(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_134,plain,
    ( v4_pre_topc(k1_setfam_1('#skF_7'),'#skF_6')
    | ~ v1_xboole_0(k1_setfam_1('#skF_7'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_109,c_131])).

tff(c_141,plain,
    ( v4_pre_topc(k1_setfam_1('#skF_7'),'#skF_6')
    | ~ v1_xboole_0(k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_134])).

tff(c_142,plain,(
    ~ v1_xboole_0(k1_setfam_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_141])).

tff(c_257,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_142])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_257])).

tff(c_264,plain,(
    k5_setfam_1(u1_struct_0('#skF_6'),k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7')) = k3_subset_1(u1_struct_0('#skF_6'),k1_setfam_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k7_setfam_1(A_25,B_26),k1_zfmisc_1(k1_zfmisc_1(A_25)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_111,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k7_setfam_1(A_53,B_54),k1_zfmisc_1(k1_zfmisc_1(A_53)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( k6_setfam_1(A_28,B_29) = k1_setfam_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k1_zfmisc_1(A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_144,plain,(
    ! [A_61,B_62] :
      ( k6_setfam_1(A_61,k7_setfam_1(A_61,B_62)) = k1_setfam_1(k7_setfam_1(A_61,B_62))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(resolution,[status(thm)],[c_111,c_34])).

tff(c_154,plain,(
    k6_setfam_1(u1_struct_0('#skF_6'),k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7')) = k1_setfam_1(k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7')) ),
    inference(resolution,[status(thm)],[c_54,c_144])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k6_setfam_1(A_23,B_24),k1_zfmisc_1(A_23))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_158,plain,
    ( m1_subset_1(k1_setfam_1(k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7')),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_26])).

tff(c_173,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_176,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(resolution,[status(thm)],[c_28,c_173])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_176])).

tff(c_182,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_410,plain,(
    ! [A_97,B_98] :
      ( v3_pre_topc(k5_setfam_1(u1_struct_0(A_97),B_98),A_97)
      | ~ v1_tops_2(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_97))))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_412,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7')),'#skF_6')
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_182,c_410])).

tff(c_423,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_6'),k1_setfam_1('#skF_7')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_216,c_264,c_412])).

tff(c_44,plain,(
    ! [B_40,A_38] :
      ( v4_pre_topc(B_40,A_38)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_38),B_40),A_38)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_431,plain,
    ( v4_pre_topc(k1_setfam_1('#skF_7'),'#skF_6')
    | ~ m1_subset_1(k1_setfam_1('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_423,c_44])).

tff(c_434,plain,(
    v4_pre_topc(k1_setfam_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_109,c_431])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_434])).

%------------------------------------------------------------------------------
