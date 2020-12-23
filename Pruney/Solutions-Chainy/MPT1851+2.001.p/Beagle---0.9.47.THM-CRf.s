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
% DateTime   : Thu Dec  3 10:28:57 EST 2020

% Result     : Theorem 8.41s
% Output     : CNFRefutation 8.41s
% Verified   : 
% Statistics : Number of formulae       :  144 (2731 expanded)
%              Number of leaves         :   33 ( 936 expanded)
%              Depth                    :   29
%              Number of atoms          :  372 (8299 expanded)
%              Number of equality atoms :   20 ( 808 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_tdlat_3(A) )
             => v2_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_126,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
      <=> u1_pre_topc(A) = k2_tarski(k1_xboole_0,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v1_tops_2(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                   => ( D = B
                     => v1_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_32,plain,(
    ! [A_40] :
      ( m1_pre_topc(A_40,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_48,plain,(
    v2_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_58,plain,(
    ! [A_60] :
      ( v2_pre_topc(A_60)
      | ~ v2_tdlat_3(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_61,plain,
    ( v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_58])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_61])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_173,plain,(
    ! [A_79,B_80] :
      ( m1_pre_topc(A_79,g1_pre_topc(u1_struct_0(B_80),u1_pre_topc(B_80)))
      | ~ m1_pre_topc(A_79,B_80)
      | ~ l1_pre_topc(B_80)
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_188,plain,(
    ! [A_79] :
      ( m1_pre_topc(A_79,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_79,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_173])).

tff(c_207,plain,(
    ! [A_82] :
      ( m1_pre_topc(A_82,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_82,'#skF_2')
      | ~ l1_pre_topc(A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_188])).

tff(c_18,plain,(
    ! [B_11,A_9] :
      ( m1_pre_topc(B_11,A_9)
      | ~ m1_pre_topc(B_11,g1_pre_topc(u1_struct_0(A_9),u1_pre_topc(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_215,plain,(
    ! [A_82] :
      ( m1_pre_topc(A_82,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_82,'#skF_2')
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_207,c_18])).

tff(c_225,plain,(
    ! [A_83] :
      ( m1_pre_topc(A_83,'#skF_1')
      | ~ m1_pre_topc(A_83,'#skF_2')
      | ~ l1_pre_topc(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_215])).

tff(c_232,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_225])).

tff(c_236,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_232])).

tff(c_151,plain,(
    ! [B_73,A_74] :
      ( m1_pre_topc(B_73,A_74)
      | ~ m1_pre_topc(B_73,g1_pre_topc(u1_struct_0(A_74),u1_pre_topc(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_154,plain,(
    ! [B_73] :
      ( m1_pre_topc(B_73,'#skF_2')
      | ~ m1_pre_topc(B_73,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_151])).

tff(c_160,plain,(
    ! [B_73] :
      ( m1_pre_topc(B_73,'#skF_2')
      | ~ m1_pre_topc(B_73,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_154])).

tff(c_179,plain,(
    ! [A_79] :
      ( m1_pre_topc(A_79,'#skF_2')
      | ~ m1_pre_topc(A_79,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_173,c_160])).

tff(c_192,plain,(
    ! [A_79] :
      ( m1_pre_topc(A_79,'#skF_2')
      | ~ m1_pre_topc(A_79,'#skF_1')
      | ~ l1_pre_topc(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_179])).

tff(c_544,plain,(
    ! [B_113,C_114,A_115] :
      ( r1_tarski(u1_struct_0(B_113),u1_struct_0(C_114))
      | ~ m1_pre_topc(B_113,C_114)
      | ~ m1_pre_topc(C_114,A_115)
      | ~ m1_pre_topc(B_113,A_115)
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_579,plain,(
    ! [B_113,A_40] :
      ( r1_tarski(u1_struct_0(B_113),u1_struct_0(A_40))
      | ~ m1_pre_topc(B_113,A_40)
      | ~ v2_pre_topc(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_32,c_544])).

tff(c_12,plain,(
    ! [A_7] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_7),u1_pre_topc(A_7)))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    ! [A_66] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_66),u1_pre_topc(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_85,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_82])).

tff(c_87,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_85])).

tff(c_88,plain,(
    ~ v2_pre_topc('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_95,plain,(
    ! [A_68] :
      ( v2_pre_topc(A_68)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_68),u1_pre_topc(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_101,plain,
    ( v2_pre_topc('#skF_2')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_95])).

tff(c_104,plain,
    ( v2_pre_topc('#skF_2')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_101])).

tff(c_105,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_104])).

tff(c_108,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_108])).

tff(c_114,plain,(
    v2_pre_topc('#skF_2') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_400,plain,(
    ! [B_102,C_103,A_104] :
      ( m1_pre_topc(B_102,C_103)
      | ~ r1_tarski(u1_struct_0(B_102),u1_struct_0(C_103))
      | ~ m1_pre_topc(C_103,A_104)
      | ~ m1_pre_topc(B_102,A_104)
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_405,plain,(
    ! [B_105,A_106] :
      ( m1_pre_topc(B_105,B_105)
      | ~ m1_pre_topc(B_105,A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_6,c_400])).

tff(c_411,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_236,c_405])).

tff(c_424,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_411])).

tff(c_548,plain,(
    ! [B_113] :
      ( r1_tarski(u1_struct_0(B_113),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_113,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_424,c_544])).

tff(c_580,plain,(
    ! [B_116] :
      ( r1_tarski(u1_struct_0(B_116),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_116,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_52,c_548])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_601,plain,(
    ! [B_122] :
      ( u1_struct_0(B_122) = u1_struct_0('#skF_2')
      | ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0(B_122))
      | ~ m1_pre_topc(B_122,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_580,c_2])).

tff(c_623,plain,(
    ! [A_123] :
      ( u1_struct_0(A_123) = u1_struct_0('#skF_2')
      | ~ m1_pre_topc(A_123,'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_123)
      | ~ v2_pre_topc(A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_579,c_601])).

tff(c_653,plain,(
    ! [A_124] :
      ( u1_struct_0(A_124) = u1_struct_0('#skF_2')
      | ~ m1_pre_topc('#skF_2',A_124)
      | ~ v2_pre_topc(A_124)
      | ~ m1_pre_topc(A_124,'#skF_1')
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_192,c_623])).

tff(c_662,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_236,c_653])).

tff(c_685,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_64,c_662])).

tff(c_700,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_685])).

tff(c_703,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_700])).

tff(c_707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_703])).

tff(c_709,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_10,plain,(
    ! [A_6] :
      ( m1_subset_1(u1_pre_topc(A_6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6))))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_380,plain,(
    ! [C_95,A_96,B_97] :
      ( m1_subset_1(C_95,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96))))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_97))))
      | ~ m1_pre_topc(B_97,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_384,plain,(
    ! [A_98,A_99] :
      ( m1_subset_1(u1_pre_topc(A_98),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_99))))
      | ~ m1_pre_topc(A_98,A_99)
      | ~ l1_pre_topc(A_99)
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_10,c_380])).

tff(c_30,plain,(
    ! [B_39,A_37] :
      ( r1_tarski(B_39,u1_pre_topc(A_37))
      | ~ v1_tops_2(B_39,A_37)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_394,plain,(
    ! [A_98,A_99] :
      ( r1_tarski(u1_pre_topc(A_98),u1_pre_topc(A_99))
      | ~ v1_tops_2(u1_pre_topc(A_98),A_99)
      | ~ m1_pre_topc(A_98,A_99)
      | ~ l1_pre_topc(A_99)
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_384,c_30])).

tff(c_44,plain,(
    ! [A_56] :
      ( k2_tarski(k1_xboole_0,u1_struct_0(A_56)) = u1_pre_topc(A_56)
      | ~ v2_tdlat_3(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_46,plain,(
    ~ v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_708,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_42,plain,(
    ! [A_56] :
      ( v2_tdlat_3(A_56)
      | k2_tarski(k1_xboole_0,u1_struct_0(A_56)) != u1_pre_topc(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_783,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_42])).

tff(c_816,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_783])).

tff(c_817,plain,(
    k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_816])).

tff(c_859,plain,
    ( u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ v2_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_817])).

tff(c_861,plain,(
    u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_859])).

tff(c_792,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_10])).

tff(c_823,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_792])).

tff(c_28,plain,(
    ! [B_39,A_37] :
      ( v1_tops_2(B_39,A_37)
      | ~ r1_tarski(B_39,u1_pre_topc(A_37))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_768,plain,(
    ! [B_39] :
      ( v1_tops_2(B_39,'#skF_2')
      | ~ r1_tarski(B_39,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_28])).

tff(c_1188,plain,(
    ! [B_142] :
      ( v1_tops_2(B_142,'#skF_2')
      | ~ r1_tarski(B_142,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_768])).

tff(c_1198,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_823,c_1188])).

tff(c_1213,plain,(
    v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1198])).

tff(c_383,plain,(
    ! [A_6,A_96] :
      ( m1_subset_1(u1_pre_topc(A_6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96))))
      | ~ m1_pre_topc(A_6,A_96)
      | ~ l1_pre_topc(A_96)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_380])).

tff(c_587,plain,(
    ! [D_117,C_118,A_119] :
      ( v1_tops_2(D_117,C_118)
      | ~ m1_subset_1(D_117,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_118))))
      | ~ v1_tops_2(D_117,A_119)
      | ~ m1_pre_topc(C_118,A_119)
      | ~ m1_subset_1(D_117,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119))))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1746,plain,(
    ! [A_159,A_160,A_161] :
      ( v1_tops_2(u1_pre_topc(A_159),A_160)
      | ~ v1_tops_2(u1_pre_topc(A_159),A_161)
      | ~ m1_pre_topc(A_160,A_161)
      | ~ m1_subset_1(u1_pre_topc(A_159),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_161))))
      | ~ l1_pre_topc(A_161)
      | ~ m1_pre_topc(A_159,A_160)
      | ~ l1_pre_topc(A_160)
      | ~ l1_pre_topc(A_159) ) ),
    inference(resolution,[status(thm)],[c_383,c_587])).

tff(c_1766,plain,(
    ! [A_159,A_79] :
      ( v1_tops_2(u1_pre_topc(A_159),A_79)
      | ~ v1_tops_2(u1_pre_topc(A_159),'#skF_2')
      | ~ m1_subset_1(u1_pre_topc(A_159),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(A_159,A_79)
      | ~ l1_pre_topc(A_159)
      | ~ m1_pre_topc(A_79,'#skF_1')
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_192,c_1746])).

tff(c_2325,plain,(
    ! [A_183,A_184] :
      ( v1_tops_2(u1_pre_topc(A_183),A_184)
      | ~ v1_tops_2(u1_pre_topc(A_183),'#skF_2')
      | ~ m1_subset_1(u1_pre_topc(A_183),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_183,A_184)
      | ~ l1_pre_topc(A_183)
      | ~ m1_pre_topc(A_184,'#skF_1')
      | ~ l1_pre_topc(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_708,c_1766])).

tff(c_2339,plain,(
    ! [A_184] :
      ( v1_tops_2(u1_pre_topc('#skF_2'),A_184)
      | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_184)
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(A_184,'#skF_1')
      | ~ l1_pre_topc(A_184) ) ),
    inference(resolution,[status(thm)],[c_823,c_2325])).

tff(c_2366,plain,(
    ! [A_185] :
      ( v1_tops_2(u1_pre_topc('#skF_2'),A_185)
      | ~ m1_pre_topc('#skF_2',A_185)
      | ~ m1_pre_topc(A_185,'#skF_1')
      | ~ l1_pre_topc(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1213,c_2339])).

tff(c_876,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_823,c_30])).

tff(c_884,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_876])).

tff(c_912,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_884])).

tff(c_2369,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2366,c_912])).

tff(c_2373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_709,c_236,c_2369])).

tff(c_2374,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_884])).

tff(c_2380,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2374,c_2])).

tff(c_2386,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_861,c_2380])).

tff(c_2389,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_394,c_2386])).

tff(c_2392,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2389])).

tff(c_2393,plain,(
    ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2392])).

tff(c_2425,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_192,c_2393])).

tff(c_2429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_709,c_2425])).

tff(c_2430,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2392])).

tff(c_2431,plain,(
    m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2392])).

tff(c_24,plain,(
    ! [C_21,A_15,B_19] :
      ( m1_subset_1(C_21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15))))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_19))))
      | ~ m1_pre_topc(B_19,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3079,plain,(
    ! [A_211,A_212,A_213] :
      ( m1_subset_1(u1_pre_topc(A_211),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_212))))
      | ~ m1_pre_topc(A_213,A_212)
      | ~ l1_pre_topc(A_212)
      | ~ m1_pre_topc(A_211,A_213)
      | ~ l1_pre_topc(A_213)
      | ~ l1_pre_topc(A_211) ) ),
    inference(resolution,[status(thm)],[c_384,c_24])).

tff(c_3097,plain,(
    ! [A_211,A_79] :
      ( m1_subset_1(u1_pre_topc(A_211),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(A_211,A_79)
      | ~ l1_pre_topc(A_211)
      | ~ m1_pre_topc(A_79,'#skF_1')
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_192,c_3079])).

tff(c_3152,plain,(
    ! [A_215,A_216] :
      ( m1_subset_1(u1_pre_topc(A_215),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_215,A_216)
      | ~ l1_pre_topc(A_215)
      | ~ m1_pre_topc(A_216,'#skF_1')
      | ~ l1_pre_topc(A_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_708,c_3097])).

tff(c_3156,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_709,c_3152])).

tff(c_3180,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_709,c_3156])).

tff(c_3213,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3180,c_28])).

tff(c_3225,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6,c_3213])).

tff(c_4037,plain,(
    ! [C_247,A_248] :
      ( m1_subset_1(C_247,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_248))))
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc('#skF_2',A_248)
      | ~ l1_pre_topc(A_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_24])).

tff(c_4061,plain,(
    ! [A_248] :
      ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_248))))
      | ~ m1_pre_topc('#skF_2',A_248)
      | ~ l1_pre_topc(A_248) ) ),
    inference(resolution,[status(thm)],[c_3180,c_4037])).

tff(c_3513,plain,(
    ! [A_228,A_229,A_230] :
      ( v1_tops_2(u1_pre_topc(A_228),A_229)
      | ~ v1_tops_2(u1_pre_topc(A_228),A_230)
      | ~ m1_pre_topc(A_229,A_230)
      | ~ m1_subset_1(u1_pre_topc(A_228),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_230))))
      | ~ l1_pre_topc(A_230)
      | ~ m1_pre_topc(A_228,A_229)
      | ~ l1_pre_topc(A_229)
      | ~ l1_pre_topc(A_228) ) ),
    inference(resolution,[status(thm)],[c_383,c_587])).

tff(c_3531,plain,(
    ! [A_228] :
      ( v1_tops_2(u1_pre_topc(A_228),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc(A_228),'#skF_1')
      | ~ m1_subset_1(u1_pre_topc(A_228),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_228,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_228) ) ),
    inference(resolution,[status(thm)],[c_236,c_3513])).

tff(c_8965,plain,(
    ! [A_377] :
      ( v1_tops_2(u1_pre_topc(A_377),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc(A_377),'#skF_1')
      | ~ m1_subset_1(u1_pre_topc(A_377),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_377,'#skF_2')
      | ~ l1_pre_topc(A_377) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_3531])).

tff(c_8996,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4061,c_8965])).

tff(c_9046,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_236,c_2431,c_3225,c_8996])).

tff(c_9048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2430,c_9046])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n021.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 11:55:04 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.41/3.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.41/3.05  
% 8.41/3.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.41/3.06  %$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.41/3.06  
% 8.41/3.06  %Foreground sorts:
% 8.41/3.06  
% 8.41/3.06  
% 8.41/3.06  %Background operators:
% 8.41/3.06  
% 8.41/3.06  
% 8.41/3.06  %Foreground operators:
% 8.41/3.06  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.41/3.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.41/3.06  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 8.41/3.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.41/3.06  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 8.41/3.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.41/3.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.41/3.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.41/3.06  tff('#skF_2', type, '#skF_2': $i).
% 8.41/3.06  tff('#skF_1', type, '#skF_1': $i).
% 8.41/3.06  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.41/3.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.41/3.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.41/3.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.41/3.06  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.41/3.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.41/3.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.41/3.06  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 8.41/3.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.41/3.06  
% 8.41/3.08  tff(f_162, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v2_tdlat_3(A)) => v2_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tex_2)).
% 8.41/3.08  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 8.41/3.08  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 8.41/3.08  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 8.41/3.08  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 8.41/3.08  tff(f_126, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 8.41/3.08  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 8.41/3.08  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_pre_topc)).
% 8.41/3.08  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.41/3.08  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 8.41/3.08  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 8.41/3.08  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 8.41/3.08  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) <=> (u1_pre_topc(A) = k2_tarski(k1_xboole_0, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tdlat_3)).
% 8.41/3.08  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_2)).
% 8.41/3.08  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.41/3.08  tff(c_32, plain, (![A_40]: (m1_pre_topc(A_40, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.41/3.08  tff(c_48, plain, (v2_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.41/3.08  tff(c_58, plain, (![A_60]: (v2_pre_topc(A_60) | ~v2_tdlat_3(A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.41/3.08  tff(c_61, plain, (v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_58])).
% 8.41/3.08  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_61])).
% 8.41/3.08  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.41/3.08  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.41/3.08  tff(c_173, plain, (![A_79, B_80]: (m1_pre_topc(A_79, g1_pre_topc(u1_struct_0(B_80), u1_pre_topc(B_80))) | ~m1_pre_topc(A_79, B_80) | ~l1_pre_topc(B_80) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.41/3.08  tff(c_188, plain, (![A_79]: (m1_pre_topc(A_79, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_79, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_79))), inference(superposition, [status(thm), theory('equality')], [c_50, c_173])).
% 8.41/3.08  tff(c_207, plain, (![A_82]: (m1_pre_topc(A_82, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_82, '#skF_2') | ~l1_pre_topc(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_188])).
% 8.41/3.08  tff(c_18, plain, (![B_11, A_9]: (m1_pre_topc(B_11, A_9) | ~m1_pre_topc(B_11, g1_pre_topc(u1_struct_0(A_9), u1_pre_topc(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.41/3.08  tff(c_215, plain, (![A_82]: (m1_pre_topc(A_82, '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_82, '#skF_2') | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_207, c_18])).
% 8.41/3.08  tff(c_225, plain, (![A_83]: (m1_pre_topc(A_83, '#skF_1') | ~m1_pre_topc(A_83, '#skF_2') | ~l1_pre_topc(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_215])).
% 8.41/3.08  tff(c_232, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_225])).
% 8.41/3.08  tff(c_236, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_232])).
% 8.41/3.08  tff(c_151, plain, (![B_73, A_74]: (m1_pre_topc(B_73, A_74) | ~m1_pre_topc(B_73, g1_pre_topc(u1_struct_0(A_74), u1_pre_topc(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.41/3.08  tff(c_154, plain, (![B_73]: (m1_pre_topc(B_73, '#skF_2') | ~m1_pre_topc(B_73, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_151])).
% 8.41/3.08  tff(c_160, plain, (![B_73]: (m1_pre_topc(B_73, '#skF_2') | ~m1_pre_topc(B_73, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_154])).
% 8.41/3.08  tff(c_179, plain, (![A_79]: (m1_pre_topc(A_79, '#skF_2') | ~m1_pre_topc(A_79, '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_173, c_160])).
% 8.41/3.08  tff(c_192, plain, (![A_79]: (m1_pre_topc(A_79, '#skF_2') | ~m1_pre_topc(A_79, '#skF_1') | ~l1_pre_topc(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_179])).
% 8.41/3.08  tff(c_544, plain, (![B_113, C_114, A_115]: (r1_tarski(u1_struct_0(B_113), u1_struct_0(C_114)) | ~m1_pre_topc(B_113, C_114) | ~m1_pre_topc(C_114, A_115) | ~m1_pre_topc(B_113, A_115) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.41/3.08  tff(c_579, plain, (![B_113, A_40]: (r1_tarski(u1_struct_0(B_113), u1_struct_0(A_40)) | ~m1_pre_topc(B_113, A_40) | ~v2_pre_topc(A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_32, c_544])).
% 8.41/3.08  tff(c_12, plain, (![A_7]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_7), u1_pre_topc(A_7))) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.41/3.08  tff(c_82, plain, (![A_66]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_66), u1_pre_topc(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.41/3.08  tff(c_85, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_50, c_82])).
% 8.41/3.08  tff(c_87, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_85])).
% 8.41/3.08  tff(c_88, plain, (~v2_pre_topc('#skF_2')), inference(splitLeft, [status(thm)], [c_87])).
% 8.41/3.08  tff(c_95, plain, (![A_68]: (v2_pre_topc(A_68) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_68), u1_pre_topc(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.41/3.08  tff(c_101, plain, (v2_pre_topc('#skF_2') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_50, c_95])).
% 8.41/3.08  tff(c_104, plain, (v2_pre_topc('#skF_2') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_101])).
% 8.41/3.08  tff(c_105, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_88, c_104])).
% 8.41/3.08  tff(c_108, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_105])).
% 8.41/3.08  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_108])).
% 8.41/3.08  tff(c_114, plain, (v2_pre_topc('#skF_2')), inference(splitRight, [status(thm)], [c_87])).
% 8.41/3.08  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.41/3.08  tff(c_400, plain, (![B_102, C_103, A_104]: (m1_pre_topc(B_102, C_103) | ~r1_tarski(u1_struct_0(B_102), u1_struct_0(C_103)) | ~m1_pre_topc(C_103, A_104) | ~m1_pre_topc(B_102, A_104) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.41/3.08  tff(c_405, plain, (![B_105, A_106]: (m1_pre_topc(B_105, B_105) | ~m1_pre_topc(B_105, A_106) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106))), inference(resolution, [status(thm)], [c_6, c_400])).
% 8.41/3.08  tff(c_411, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_236, c_405])).
% 8.41/3.08  tff(c_424, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_411])).
% 8.41/3.08  tff(c_548, plain, (![B_113]: (r1_tarski(u1_struct_0(B_113), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_113, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_424, c_544])).
% 8.41/3.08  tff(c_580, plain, (![B_116]: (r1_tarski(u1_struct_0(B_116), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_116, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_52, c_548])).
% 8.41/3.08  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.41/3.08  tff(c_601, plain, (![B_122]: (u1_struct_0(B_122)=u1_struct_0('#skF_2') | ~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0(B_122)) | ~m1_pre_topc(B_122, '#skF_2'))), inference(resolution, [status(thm)], [c_580, c_2])).
% 8.41/3.08  tff(c_623, plain, (![A_123]: (u1_struct_0(A_123)=u1_struct_0('#skF_2') | ~m1_pre_topc(A_123, '#skF_2') | ~m1_pre_topc('#skF_2', A_123) | ~v2_pre_topc(A_123) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_579, c_601])).
% 8.41/3.08  tff(c_653, plain, (![A_124]: (u1_struct_0(A_124)=u1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', A_124) | ~v2_pre_topc(A_124) | ~m1_pre_topc(A_124, '#skF_1') | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_192, c_623])).
% 8.41/3.08  tff(c_662, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_236, c_653])).
% 8.41/3.08  tff(c_685, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_64, c_662])).
% 8.41/3.08  tff(c_700, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_685])).
% 8.41/3.08  tff(c_703, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_700])).
% 8.41/3.08  tff(c_707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_703])).
% 8.41/3.08  tff(c_709, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_685])).
% 8.41/3.08  tff(c_10, plain, (![A_6]: (m1_subset_1(u1_pre_topc(A_6), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6)))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.41/3.08  tff(c_380, plain, (![C_95, A_96, B_97]: (m1_subset_1(C_95, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96)))) | ~m1_subset_1(C_95, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_97)))) | ~m1_pre_topc(B_97, A_96) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.41/3.08  tff(c_384, plain, (![A_98, A_99]: (m1_subset_1(u1_pre_topc(A_98), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_99)))) | ~m1_pre_topc(A_98, A_99) | ~l1_pre_topc(A_99) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_10, c_380])).
% 8.41/3.08  tff(c_30, plain, (![B_39, A_37]: (r1_tarski(B_39, u1_pre_topc(A_37)) | ~v1_tops_2(B_39, A_37) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.41/3.08  tff(c_394, plain, (![A_98, A_99]: (r1_tarski(u1_pre_topc(A_98), u1_pre_topc(A_99)) | ~v1_tops_2(u1_pre_topc(A_98), A_99) | ~m1_pre_topc(A_98, A_99) | ~l1_pre_topc(A_99) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_384, c_30])).
% 8.41/3.08  tff(c_44, plain, (![A_56]: (k2_tarski(k1_xboole_0, u1_struct_0(A_56))=u1_pre_topc(A_56) | ~v2_tdlat_3(A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.41/3.08  tff(c_46, plain, (~v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.41/3.08  tff(c_708, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_685])).
% 8.41/3.08  tff(c_42, plain, (![A_56]: (v2_tdlat_3(A_56) | k2_tarski(k1_xboole_0, u1_struct_0(A_56))!=u1_pre_topc(A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.41/3.08  tff(c_783, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_708, c_42])).
% 8.41/3.08  tff(c_816, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_783])).
% 8.41/3.08  tff(c_817, plain, (k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_816])).
% 8.41/3.08  tff(c_859, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1') | ~v2_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_44, c_817])).
% 8.41/3.08  tff(c_861, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_859])).
% 8.41/3.08  tff(c_792, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_708, c_10])).
% 8.41/3.08  tff(c_823, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_792])).
% 8.41/3.08  tff(c_28, plain, (![B_39, A_37]: (v1_tops_2(B_39, A_37) | ~r1_tarski(B_39, u1_pre_topc(A_37)) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.41/3.08  tff(c_768, plain, (![B_39]: (v1_tops_2(B_39, '#skF_2') | ~r1_tarski(B_39, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_708, c_28])).
% 8.41/3.08  tff(c_1188, plain, (![B_142]: (v1_tops_2(B_142, '#skF_2') | ~r1_tarski(B_142, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_142, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_768])).
% 8.41/3.08  tff(c_1198, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_823, c_1188])).
% 8.41/3.08  tff(c_1213, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1198])).
% 8.41/3.08  tff(c_383, plain, (![A_6, A_96]: (m1_subset_1(u1_pre_topc(A_6), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96)))) | ~m1_pre_topc(A_6, A_96) | ~l1_pre_topc(A_96) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_10, c_380])).
% 8.41/3.08  tff(c_587, plain, (![D_117, C_118, A_119]: (v1_tops_2(D_117, C_118) | ~m1_subset_1(D_117, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_118)))) | ~v1_tops_2(D_117, A_119) | ~m1_pre_topc(C_118, A_119) | ~m1_subset_1(D_117, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119)))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.41/3.08  tff(c_1746, plain, (![A_159, A_160, A_161]: (v1_tops_2(u1_pre_topc(A_159), A_160) | ~v1_tops_2(u1_pre_topc(A_159), A_161) | ~m1_pre_topc(A_160, A_161) | ~m1_subset_1(u1_pre_topc(A_159), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_161)))) | ~l1_pre_topc(A_161) | ~m1_pre_topc(A_159, A_160) | ~l1_pre_topc(A_160) | ~l1_pre_topc(A_159))), inference(resolution, [status(thm)], [c_383, c_587])).
% 8.41/3.08  tff(c_1766, plain, (![A_159, A_79]: (v1_tops_2(u1_pre_topc(A_159), A_79) | ~v1_tops_2(u1_pre_topc(A_159), '#skF_2') | ~m1_subset_1(u1_pre_topc(A_159), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(A_159, A_79) | ~l1_pre_topc(A_159) | ~m1_pre_topc(A_79, '#skF_1') | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_192, c_1746])).
% 8.41/3.08  tff(c_2325, plain, (![A_183, A_184]: (v1_tops_2(u1_pre_topc(A_183), A_184) | ~v1_tops_2(u1_pre_topc(A_183), '#skF_2') | ~m1_subset_1(u1_pre_topc(A_183), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_183, A_184) | ~l1_pre_topc(A_183) | ~m1_pre_topc(A_184, '#skF_1') | ~l1_pre_topc(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_708, c_1766])).
% 8.41/3.08  tff(c_2339, plain, (![A_184]: (v1_tops_2(u1_pre_topc('#skF_2'), A_184) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~m1_pre_topc('#skF_2', A_184) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(A_184, '#skF_1') | ~l1_pre_topc(A_184))), inference(resolution, [status(thm)], [c_823, c_2325])).
% 8.41/3.08  tff(c_2366, plain, (![A_185]: (v1_tops_2(u1_pre_topc('#skF_2'), A_185) | ~m1_pre_topc('#skF_2', A_185) | ~m1_pre_topc(A_185, '#skF_1') | ~l1_pre_topc(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1213, c_2339])).
% 8.41/3.08  tff(c_876, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_823, c_30])).
% 8.41/3.08  tff(c_884, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_876])).
% 8.41/3.08  tff(c_912, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_884])).
% 8.41/3.08  tff(c_2369, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2366, c_912])).
% 8.41/3.08  tff(c_2373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_709, c_236, c_2369])).
% 8.41/3.08  tff(c_2374, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_884])).
% 8.41/3.08  tff(c_2380, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_2374, c_2])).
% 8.41/3.08  tff(c_2386, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_861, c_2380])).
% 8.41/3.08  tff(c_2389, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_394, c_2386])).
% 8.41/3.08  tff(c_2392, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~m1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2389])).
% 8.41/3.08  tff(c_2393, plain, (~m1_pre_topc('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_2392])).
% 8.41/3.08  tff(c_2425, plain, (~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_192, c_2393])).
% 8.41/3.08  tff(c_2429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_709, c_2425])).
% 8.41/3.08  tff(c_2430, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_2392])).
% 8.41/3.08  tff(c_2431, plain, (m1_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_2392])).
% 8.41/3.08  tff(c_24, plain, (![C_21, A_15, B_19]: (m1_subset_1(C_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15)))) | ~m1_subset_1(C_21, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_19)))) | ~m1_pre_topc(B_19, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.41/3.08  tff(c_3079, plain, (![A_211, A_212, A_213]: (m1_subset_1(u1_pre_topc(A_211), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_212)))) | ~m1_pre_topc(A_213, A_212) | ~l1_pre_topc(A_212) | ~m1_pre_topc(A_211, A_213) | ~l1_pre_topc(A_213) | ~l1_pre_topc(A_211))), inference(resolution, [status(thm)], [c_384, c_24])).
% 8.41/3.08  tff(c_3097, plain, (![A_211, A_79]: (m1_subset_1(u1_pre_topc(A_211), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(A_211, A_79) | ~l1_pre_topc(A_211) | ~m1_pre_topc(A_79, '#skF_1') | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_192, c_3079])).
% 8.41/3.08  tff(c_3152, plain, (![A_215, A_216]: (m1_subset_1(u1_pre_topc(A_215), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_215, A_216) | ~l1_pre_topc(A_215) | ~m1_pre_topc(A_216, '#skF_1') | ~l1_pre_topc(A_216))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_708, c_3097])).
% 8.41/3.08  tff(c_3156, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_709, c_3152])).
% 8.41/3.08  tff(c_3180, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_709, c_3156])).
% 8.41/3.08  tff(c_3213, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3180, c_28])).
% 8.41/3.08  tff(c_3225, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6, c_3213])).
% 8.41/3.08  tff(c_4037, plain, (![C_247, A_248]: (m1_subset_1(C_247, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_248)))) | ~m1_subset_1(C_247, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_2', A_248) | ~l1_pre_topc(A_248))), inference(superposition, [status(thm), theory('equality')], [c_708, c_24])).
% 8.41/3.08  tff(c_4061, plain, (![A_248]: (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_248)))) | ~m1_pre_topc('#skF_2', A_248) | ~l1_pre_topc(A_248))), inference(resolution, [status(thm)], [c_3180, c_4037])).
% 8.41/3.08  tff(c_3513, plain, (![A_228, A_229, A_230]: (v1_tops_2(u1_pre_topc(A_228), A_229) | ~v1_tops_2(u1_pre_topc(A_228), A_230) | ~m1_pre_topc(A_229, A_230) | ~m1_subset_1(u1_pre_topc(A_228), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_230)))) | ~l1_pre_topc(A_230) | ~m1_pre_topc(A_228, A_229) | ~l1_pre_topc(A_229) | ~l1_pre_topc(A_228))), inference(resolution, [status(thm)], [c_383, c_587])).
% 8.41/3.08  tff(c_3531, plain, (![A_228]: (v1_tops_2(u1_pre_topc(A_228), '#skF_2') | ~v1_tops_2(u1_pre_topc(A_228), '#skF_1') | ~m1_subset_1(u1_pre_topc(A_228), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_228, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_228))), inference(resolution, [status(thm)], [c_236, c_3513])).
% 8.41/3.08  tff(c_8965, plain, (![A_377]: (v1_tops_2(u1_pre_topc(A_377), '#skF_2') | ~v1_tops_2(u1_pre_topc(A_377), '#skF_1') | ~m1_subset_1(u1_pre_topc(A_377), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_377, '#skF_2') | ~l1_pre_topc(A_377))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_3531])).
% 8.41/3.08  tff(c_8996, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4061, c_8965])).
% 8.41/3.08  tff(c_9046, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_236, c_2431, c_3225, c_8996])).
% 8.41/3.08  tff(c_9048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2430, c_9046])).
% 8.41/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.41/3.08  
% 8.41/3.08  Inference rules
% 8.41/3.08  ----------------------
% 8.41/3.08  #Ref     : 0
% 8.41/3.08  #Sup     : 1744
% 8.41/3.08  #Fact    : 0
% 8.41/3.08  #Define  : 0
% 8.41/3.08  #Split   : 8
% 8.41/3.08  #Chain   : 0
% 8.41/3.08  #Close   : 0
% 8.41/3.08  
% 8.41/3.08  Ordering : KBO
% 8.41/3.08  
% 8.41/3.08  Simplification rules
% 8.41/3.08  ----------------------
% 8.41/3.08  #Subsume      : 541
% 8.41/3.08  #Demod        : 2937
% 8.41/3.08  #Tautology    : 573
% 8.41/3.08  #SimpNegUnit  : 55
% 8.41/3.08  #BackRed      : 7
% 8.41/3.08  
% 8.41/3.08  #Partial instantiations: 0
% 8.41/3.08  #Strategies tried      : 1
% 8.41/3.08  
% 8.41/3.08  Timing (in seconds)
% 8.41/3.08  ----------------------
% 8.41/3.08  Preprocessing        : 0.54
% 8.41/3.08  Parsing              : 0.28
% 8.41/3.08  CNF conversion       : 0.04
% 8.41/3.08  Main loop            : 1.66
% 8.41/3.08  Inferencing          : 0.47
% 8.41/3.08  Reduction            : 0.55
% 8.41/3.08  Demodulation         : 0.39
% 8.41/3.08  BG Simplification    : 0.06
% 8.41/3.08  Subsumption          : 0.48
% 8.41/3.08  Abstraction          : 0.08
% 8.41/3.08  MUC search           : 0.00
% 8.41/3.08  Cooper               : 0.00
% 8.41/3.08  Total                : 2.25
% 8.41/3.08  Index Insertion      : 0.00
% 8.41/3.08  Index Deletion       : 0.00
% 8.41/3.08  Index Matching       : 0.00
% 8.41/3.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
