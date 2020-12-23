%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:26 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 172 expanded)
%              Number of leaves         :   46 (  80 expanded)
%              Depth                    :    8
%              Number of atoms          :  170 ( 515 expanded)
%              Number of equality atoms :   23 (  40 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_56,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( ( v3_pre_topc(B,A)
                  | v4_pre_topc(B,A) )
                & v3_tex_2(B,A)
                & v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_113,plain,(
    ! [B_49,A_50] :
      ( ~ r1_xboole_0(B_49,A_50)
      | ~ r1_tarski(B_49,A_50)
      | v1_xboole_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    ! [A_51] :
      ( ~ r1_tarski(A_51,k1_xboole_0)
      | v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_4,c_113])).

tff(c_123,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_118])).

tff(c_20,plain,(
    ! [A_10] : k1_subset_1(A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_subset_1(A_15)) = k2_subset_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_75,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_subset_1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28])).

tff(c_77,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_75])).

tff(c_24,plain,(
    ! [A_12] : m1_subset_1(k1_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_137,plain,(
    ! [A_56,B_57] :
      ( k3_subset_1(A_56,k3_subset_1(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_141,plain,(
    ! [A_12] : k3_subset_1(A_12,k3_subset_1(A_12,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_137])).

tff(c_144,plain,(
    ! [A_12] : k3_subset_1(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_141])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_68,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_226,plain,(
    ! [A_74,B_75] :
      ( k2_pre_topc(A_74,B_75) = B_75
      | ~ v4_pre_topc(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_235,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_226])).

tff(c_244,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_235])).

tff(c_246,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_72,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_70,plain,(
    v3_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_64,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_106,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_364,plain,(
    ! [B_94,A_95] :
      ( v4_pre_topc(B_94,A_95)
      | ~ v3_pre_topc(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v3_tdlat_3(A_95)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_373,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ v3_pre_topc('#skF_6','#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_364])).

tff(c_382,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_70,c_106,c_373])).

tff(c_384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_382])).

tff(c_385,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_394,plain,(
    ! [A_99,B_100] :
      ( k2_pre_topc(A_99,B_100) = u1_struct_0(A_99)
      | ~ v1_tops_1(B_100,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_403,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = u1_struct_0('#skF_5')
    | ~ v1_tops_1('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_394])).

tff(c_412,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_385,c_403])).

tff(c_414,plain,(
    ~ v1_tops_1('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_62,plain,(
    v3_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_548,plain,(
    ! [B_121,A_122] :
      ( v1_tops_1(B_121,A_122)
      | ~ v3_tex_2(B_121,A_122)
      | ~ v3_pre_topc(B_121,A_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_557,plain,
    ( v1_tops_1('#skF_6','#skF_5')
    | ~ v3_tex_2('#skF_6','#skF_5')
    | ~ v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_548])).

tff(c_566,plain,
    ( v1_tops_1('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_106,c_62,c_557])).

tff(c_568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_414,c_566])).

tff(c_569,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_60,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_124,plain,(
    ! [B_52,A_53] :
      ( ~ v1_subset_1(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_127,plain,
    ( ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_124])).

tff(c_133,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_127])).

tff(c_185,plain,(
    ! [A_64,B_65] :
      ( ~ v1_xboole_0(k3_subset_1(A_64,B_65))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64))
      | ~ v1_subset_1(B_65,A_64)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_194,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_5'),'#skF_6'))
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_185])).

tff(c_202,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_5'),'#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_194])).

tff(c_203,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_5'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_202])).

tff(c_571,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_203])).

tff(c_578,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_144,c_571])).

tff(c_580,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_579,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_795,plain,(
    ! [B_165,A_166] :
      ( v3_pre_topc(B_165,A_166)
      | ~ v4_pre_topc(B_165,A_166)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ v3_tdlat_3(A_166)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_804,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ v4_pre_topc('#skF_6','#skF_5')
    | ~ v3_tdlat_3('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_795])).

tff(c_813,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_70,c_579,c_804])).

tff(c_815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_580,c_813])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:07:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.50  
% 3.09/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.50  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 3.09/1.50  
% 3.09/1.50  %Foreground sorts:
% 3.09/1.50  
% 3.09/1.50  
% 3.09/1.50  %Background operators:
% 3.09/1.50  
% 3.09/1.50  
% 3.09/1.50  %Foreground operators:
% 3.09/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.09/1.50  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.09/1.50  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.09/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.50  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.09/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.09/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.09/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.09/1.50  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.09/1.50  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.09/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.09/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.09/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.50  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.09/1.50  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.09/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.50  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.09/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.09/1.50  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.09/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.09/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.09/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.09/1.50  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.09/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.09/1.50  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.09/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.50  
% 3.09/1.52  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.09/1.52  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.09/1.52  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.09/1.52  tff(f_46, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.09/1.52  tff(f_48, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.09/1.52  tff(f_56, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.09/1.52  tff(f_50, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 3.09/1.52  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.09/1.52  tff(f_162, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 3.09/1.52  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.09/1.52  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 3.09/1.52  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 3.09/1.52  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 3.09/1.52  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 3.09/1.52  tff(f_98, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tex_2)).
% 3.09/1.52  tff(f_124, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.09/1.52  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.09/1.52  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.09/1.52  tff(c_113, plain, (![B_49, A_50]: (~r1_xboole_0(B_49, A_50) | ~r1_tarski(B_49, A_50) | v1_xboole_0(B_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.09/1.52  tff(c_118, plain, (![A_51]: (~r1_tarski(A_51, k1_xboole_0) | v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_4, c_113])).
% 3.09/1.52  tff(c_123, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_118])).
% 3.09/1.52  tff(c_20, plain, (![A_10]: (k1_subset_1(A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.09/1.52  tff(c_22, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.09/1.52  tff(c_28, plain, (![A_15]: (k3_subset_1(A_15, k1_subset_1(A_15))=k2_subset_1(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.09/1.52  tff(c_75, plain, (![A_15]: (k3_subset_1(A_15, k1_subset_1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28])).
% 3.09/1.52  tff(c_77, plain, (![A_15]: (k3_subset_1(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_75])).
% 3.09/1.52  tff(c_24, plain, (![A_12]: (m1_subset_1(k1_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.09/1.52  tff(c_76, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 3.09/1.52  tff(c_137, plain, (![A_56, B_57]: (k3_subset_1(A_56, k3_subset_1(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.09/1.52  tff(c_141, plain, (![A_12]: (k3_subset_1(A_12, k3_subset_1(A_12, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_76, c_137])).
% 3.09/1.52  tff(c_144, plain, (![A_12]: (k3_subset_1(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_141])).
% 3.09/1.52  tff(c_74, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.09/1.52  tff(c_68, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.09/1.52  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.09/1.52  tff(c_226, plain, (![A_74, B_75]: (k2_pre_topc(A_74, B_75)=B_75 | ~v4_pre_topc(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.09/1.52  tff(c_235, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6' | ~v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_226])).
% 3.09/1.52  tff(c_244, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6' | ~v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_235])).
% 3.09/1.52  tff(c_246, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_244])).
% 3.09/1.52  tff(c_72, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.09/1.52  tff(c_70, plain, (v3_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.09/1.52  tff(c_64, plain, (v4_pre_topc('#skF_6', '#skF_5') | v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.09/1.52  tff(c_106, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_64])).
% 3.09/1.52  tff(c_364, plain, (![B_94, A_95]: (v4_pre_topc(B_94, A_95) | ~v3_pre_topc(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~v3_tdlat_3(A_95) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.09/1.52  tff(c_373, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~v3_pre_topc('#skF_6', '#skF_5') | ~v3_tdlat_3('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_364])).
% 3.09/1.52  tff(c_382, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_70, c_106, c_373])).
% 3.09/1.52  tff(c_384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_382])).
% 3.09/1.52  tff(c_385, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_244])).
% 3.09/1.52  tff(c_394, plain, (![A_99, B_100]: (k2_pre_topc(A_99, B_100)=u1_struct_0(A_99) | ~v1_tops_1(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.09/1.52  tff(c_403, plain, (k2_pre_topc('#skF_5', '#skF_6')=u1_struct_0('#skF_5') | ~v1_tops_1('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_394])).
% 3.09/1.52  tff(c_412, plain, (u1_struct_0('#skF_5')='#skF_6' | ~v1_tops_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_385, c_403])).
% 3.09/1.52  tff(c_414, plain, (~v1_tops_1('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_412])).
% 3.09/1.52  tff(c_62, plain, (v3_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.09/1.52  tff(c_548, plain, (![B_121, A_122]: (v1_tops_1(B_121, A_122) | ~v3_tex_2(B_121, A_122) | ~v3_pre_topc(B_121, A_122) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.09/1.52  tff(c_557, plain, (v1_tops_1('#skF_6', '#skF_5') | ~v3_tex_2('#skF_6', '#skF_5') | ~v3_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_548])).
% 3.09/1.52  tff(c_566, plain, (v1_tops_1('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_106, c_62, c_557])).
% 3.09/1.52  tff(c_568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_414, c_566])).
% 3.09/1.52  tff(c_569, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_412])).
% 3.09/1.52  tff(c_60, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.09/1.52  tff(c_124, plain, (![B_52, A_53]: (~v1_subset_1(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.09/1.52  tff(c_127, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_124])).
% 3.09/1.52  tff(c_133, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_127])).
% 3.09/1.52  tff(c_185, plain, (![A_64, B_65]: (~v1_xboole_0(k3_subset_1(A_64, B_65)) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)) | ~v1_subset_1(B_65, A_64) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.09/1.52  tff(c_194, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_5'), '#skF_6')) | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_185])).
% 3.09/1.52  tff(c_202, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_5'), '#skF_6')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_194])).
% 3.09/1.52  tff(c_203, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_5'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_133, c_202])).
% 3.09/1.52  tff(c_571, plain, (~v1_xboole_0(k3_subset_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_203])).
% 3.09/1.52  tff(c_578, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_144, c_571])).
% 3.09/1.52  tff(c_580, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 3.09/1.52  tff(c_579, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 3.09/1.52  tff(c_795, plain, (![B_165, A_166]: (v3_pre_topc(B_165, A_166) | ~v4_pre_topc(B_165, A_166) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~v3_tdlat_3(A_166) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.09/1.52  tff(c_804, plain, (v3_pre_topc('#skF_6', '#skF_5') | ~v4_pre_topc('#skF_6', '#skF_5') | ~v3_tdlat_3('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_795])).
% 3.09/1.52  tff(c_813, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_70, c_579, c_804])).
% 3.09/1.52  tff(c_815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_580, c_813])).
% 3.09/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.52  
% 3.09/1.52  Inference rules
% 3.09/1.52  ----------------------
% 3.09/1.52  #Ref     : 0
% 3.09/1.52  #Sup     : 143
% 3.09/1.52  #Fact    : 0
% 3.09/1.52  #Define  : 0
% 3.09/1.52  #Split   : 5
% 3.09/1.52  #Chain   : 0
% 3.09/1.52  #Close   : 0
% 3.09/1.52  
% 3.09/1.52  Ordering : KBO
% 3.09/1.52  
% 3.09/1.52  Simplification rules
% 3.09/1.52  ----------------------
% 3.09/1.52  #Subsume      : 17
% 3.09/1.52  #Demod        : 68
% 3.09/1.52  #Tautology    : 44
% 3.09/1.52  #SimpNegUnit  : 9
% 3.09/1.52  #BackRed      : 5
% 3.09/1.52  
% 3.09/1.52  #Partial instantiations: 0
% 3.09/1.52  #Strategies tried      : 1
% 3.09/1.52  
% 3.09/1.52  Timing (in seconds)
% 3.09/1.52  ----------------------
% 3.09/1.52  Preprocessing        : 0.35
% 3.09/1.52  Parsing              : 0.19
% 3.09/1.52  CNF conversion       : 0.02
% 3.09/1.52  Main loop            : 0.35
% 3.09/1.52  Inferencing          : 0.14
% 3.09/1.52  Reduction            : 0.10
% 3.09/1.52  Demodulation         : 0.07
% 3.09/1.52  BG Simplification    : 0.02
% 3.09/1.52  Subsumption          : 0.05
% 3.09/1.52  Abstraction          : 0.02
% 3.09/1.52  MUC search           : 0.00
% 3.09/1.52  Cooper               : 0.00
% 3.09/1.52  Total                : 0.73
% 3.09/1.52  Index Insertion      : 0.00
% 3.09/1.52  Index Deletion       : 0.00
% 3.09/1.52  Index Matching       : 0.00
% 3.09/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
