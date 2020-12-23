%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:05 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 291 expanded)
%              Number of leaves         :   38 ( 120 expanded)
%              Depth                    :   12
%              Number of atoms          :  166 ( 735 expanded)
%              Number of equality atoms :   33 ( 139 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_66,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_48,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_57,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_279,plain,(
    ! [A_77,B_78] :
      ( k1_tops_1(A_77,B_78) = k1_xboole_0
      | ~ v2_tops_1(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_290,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_279])).

tff(c_295,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_290])).

tff(c_296,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_58,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_54])).

tff(c_476,plain,(
    ! [B_102,A_103] :
      ( v2_tops_1(B_102,A_103)
      | ~ r1_tarski(B_102,k2_tops_1(A_103,B_102))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_480,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_476])).

tff(c_483,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_6,c_480])).

tff(c_485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_483])).

tff(c_487,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_42,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_793,plain,(
    ! [B_141,A_142] :
      ( v3_tops_1(B_141,A_142)
      | ~ v4_pre_topc(B_141,A_142)
      | ~ v2_tops_1(B_141,A_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_804,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_793])).

tff(c_809,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_487,c_42,c_804])).

tff(c_811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_809])).

tff(c_813,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_968,plain,(
    ! [B_173,A_174] :
      ( v2_tops_1(B_173,A_174)
      | ~ v3_tops_1(B_173,A_174)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_979,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_968])).

tff(c_984,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_813,c_979])).

tff(c_1054,plain,(
    ! [A_185,B_186] :
      ( k1_tops_1(A_185,B_186) = k1_xboole_0
      | ~ v2_tops_1(B_186,A_185)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1065,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1054])).

tff(c_1070,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_984,c_1065])).

tff(c_923,plain,(
    ! [A_166,B_167] :
      ( r1_tarski(k1_tops_1(A_166,B_167),B_167)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_931,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_923])).

tff(c_936,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_931])).

tff(c_1074,plain,(
    r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1070,c_936])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_812,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1151,plain,(
    ! [B_193,A_194] :
      ( r1_tarski(B_193,k2_tops_1(A_194,B_193))
      | ~ v2_tops_1(B_193,A_194)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1159,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1151])).

tff(c_1164,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_984,c_1159])).

tff(c_864,plain,(
    ! [A_157,B_158] :
      ( k4_xboole_0(A_157,B_158) = k3_subset_1(A_157,B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_875,plain,(
    ! [B_15,A_14] :
      ( k4_xboole_0(B_15,A_14) = k3_subset_1(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_20,c_864])).

tff(c_1092,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_subset_1('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1074,c_875])).

tff(c_881,plain,(
    ! [A_159,B_160,C_161] :
      ( k7_subset_1(A_159,B_160,C_161) = k4_xboole_0(B_160,C_161)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(A_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_890,plain,(
    ! [C_161] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_161) = k4_xboole_0('#skF_2',C_161) ),
    inference(resolution,[status(thm)],[c_44,c_881])).

tff(c_1033,plain,(
    ! [A_183,B_184] :
      ( k2_pre_topc(A_183,B_184) = B_184
      | ~ v4_pre_topc(B_184,A_183)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1044,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1033])).

tff(c_1049,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_1044])).

tff(c_1370,plain,(
    ! [A_221,B_222] :
      ( k7_subset_1(u1_struct_0(A_221),k2_pre_topc(A_221,B_222),k1_tops_1(A_221,B_222)) = k2_tops_1(A_221,B_222)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1379,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1070,c_1370])).

tff(c_1386,plain,(
    k3_subset_1('#skF_2',k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1092,c_890,c_1049,c_1379])).

tff(c_855,plain,(
    ! [A_153,B_154] :
      ( m1_subset_1(k3_subset_1(A_153,B_154),k1_zfmisc_1(A_153))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_860,plain,(
    ! [A_155,B_156] :
      ( r1_tarski(k3_subset_1(A_155,B_156),A_155)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155)) ) ),
    inference(resolution,[status(thm)],[c_855,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_863,plain,(
    ! [A_155,B_156] :
      ( k3_subset_1(A_155,B_156) = A_155
      | ~ r1_tarski(A_155,k3_subset_1(A_155,B_156))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155)) ) ),
    inference(resolution,[status(thm)],[c_860,c_2])).

tff(c_1399,plain,
    ( k3_subset_1('#skF_2',k1_xboole_0) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1386,c_863])).

tff(c_1413,plain,
    ( k2_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1164,c_1386,c_1399])).

tff(c_1414,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_812,c_1413])).

tff(c_1419,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1414])).

tff(c_1423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_1419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:21:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.60  
% 3.14/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.60  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.14/1.60  
% 3.14/1.60  %Foreground sorts:
% 3.14/1.60  
% 3.14/1.60  
% 3.14/1.60  %Background operators:
% 3.14/1.60  
% 3.14/1.60  
% 3.14/1.60  %Foreground operators:
% 3.14/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.60  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.14/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.60  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.14/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.14/1.60  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.14/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.14/1.60  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.14/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.60  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.14/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.60  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.14/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.14/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.60  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.14/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.14/1.60  
% 3.44/1.62  tff(f_130, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 3.44/1.62  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.44/1.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.44/1.62  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 3.44/1.62  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_tops_1)).
% 3.44/1.62  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 3.44/1.62  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.44/1.62  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.44/1.62  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.44/1.62  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.44/1.62  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.44/1.62  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.44/1.62  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.44/1.62  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.44/1.62  tff(c_48, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.44/1.62  tff(c_57, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 3.44/1.62  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.44/1.62  tff(c_279, plain, (![A_77, B_78]: (k1_tops_1(A_77, B_78)=k1_xboole_0 | ~v2_tops_1(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.44/1.62  tff(c_290, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_279])).
% 3.44/1.62  tff(c_295, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_290])).
% 3.44/1.62  tff(c_296, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_295])).
% 3.44/1.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.62  tff(c_54, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.44/1.62  tff(c_58, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_57, c_54])).
% 3.44/1.62  tff(c_476, plain, (![B_102, A_103]: (v2_tops_1(B_102, A_103) | ~r1_tarski(B_102, k2_tops_1(A_103, B_102)) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.44/1.62  tff(c_480, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_58, c_476])).
% 3.44/1.62  tff(c_483, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_6, c_480])).
% 3.44/1.62  tff(c_485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_296, c_483])).
% 3.44/1.62  tff(c_487, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_295])).
% 3.44/1.62  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.44/1.62  tff(c_793, plain, (![B_141, A_142]: (v3_tops_1(B_141, A_142) | ~v4_pre_topc(B_141, A_142) | ~v2_tops_1(B_141, A_142) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.44/1.62  tff(c_804, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_793])).
% 3.44/1.62  tff(c_809, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_487, c_42, c_804])).
% 3.44/1.62  tff(c_811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_809])).
% 3.44/1.62  tff(c_813, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 3.44/1.62  tff(c_968, plain, (![B_173, A_174]: (v2_tops_1(B_173, A_174) | ~v3_tops_1(B_173, A_174) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.44/1.62  tff(c_979, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_968])).
% 3.44/1.62  tff(c_984, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_813, c_979])).
% 3.44/1.62  tff(c_1054, plain, (![A_185, B_186]: (k1_tops_1(A_185, B_186)=k1_xboole_0 | ~v2_tops_1(B_186, A_185) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.44/1.62  tff(c_1065, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1054])).
% 3.44/1.62  tff(c_1070, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_984, c_1065])).
% 3.44/1.62  tff(c_923, plain, (![A_166, B_167]: (r1_tarski(k1_tops_1(A_166, B_167), B_167) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.44/1.62  tff(c_931, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_923])).
% 3.44/1.62  tff(c_936, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_931])).
% 3.44/1.62  tff(c_1074, plain, (r1_tarski(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1070, c_936])).
% 3.44/1.62  tff(c_20, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.44/1.62  tff(c_812, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 3.44/1.62  tff(c_1151, plain, (![B_193, A_194]: (r1_tarski(B_193, k2_tops_1(A_194, B_193)) | ~v2_tops_1(B_193, A_194) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.44/1.62  tff(c_1159, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1151])).
% 3.44/1.62  tff(c_1164, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_984, c_1159])).
% 3.44/1.62  tff(c_864, plain, (![A_157, B_158]: (k4_xboole_0(A_157, B_158)=k3_subset_1(A_157, B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(A_157)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.62  tff(c_875, plain, (![B_15, A_14]: (k4_xboole_0(B_15, A_14)=k3_subset_1(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_20, c_864])).
% 3.44/1.62  tff(c_1092, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_subset_1('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_1074, c_875])).
% 3.44/1.62  tff(c_881, plain, (![A_159, B_160, C_161]: (k7_subset_1(A_159, B_160, C_161)=k4_xboole_0(B_160, C_161) | ~m1_subset_1(B_160, k1_zfmisc_1(A_159)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.44/1.62  tff(c_890, plain, (![C_161]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_161)=k4_xboole_0('#skF_2', C_161))), inference(resolution, [status(thm)], [c_44, c_881])).
% 3.44/1.62  tff(c_1033, plain, (![A_183, B_184]: (k2_pre_topc(A_183, B_184)=B_184 | ~v4_pre_topc(B_184, A_183) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.44/1.62  tff(c_1044, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1033])).
% 3.44/1.62  tff(c_1049, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_1044])).
% 3.44/1.62  tff(c_1370, plain, (![A_221, B_222]: (k7_subset_1(u1_struct_0(A_221), k2_pre_topc(A_221, B_222), k1_tops_1(A_221, B_222))=k2_tops_1(A_221, B_222) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.44/1.62  tff(c_1379, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1070, c_1370])).
% 3.44/1.62  tff(c_1386, plain, (k3_subset_1('#skF_2', k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1092, c_890, c_1049, c_1379])).
% 3.44/1.62  tff(c_855, plain, (![A_153, B_154]: (m1_subset_1(k3_subset_1(A_153, B_154), k1_zfmisc_1(A_153)) | ~m1_subset_1(B_154, k1_zfmisc_1(A_153)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.44/1.62  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.44/1.62  tff(c_860, plain, (![A_155, B_156]: (r1_tarski(k3_subset_1(A_155, B_156), A_155) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)))), inference(resolution, [status(thm)], [c_855, c_18])).
% 3.44/1.62  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.62  tff(c_863, plain, (![A_155, B_156]: (k3_subset_1(A_155, B_156)=A_155 | ~r1_tarski(A_155, k3_subset_1(A_155, B_156)) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)))), inference(resolution, [status(thm)], [c_860, c_2])).
% 3.44/1.62  tff(c_1399, plain, (k3_subset_1('#skF_2', k1_xboole_0)='#skF_2' | ~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1386, c_863])).
% 3.44/1.62  tff(c_1413, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2' | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1164, c_1386, c_1399])).
% 3.44/1.62  tff(c_1414, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_812, c_1413])).
% 3.44/1.62  tff(c_1419, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_20, c_1414])).
% 3.44/1.62  tff(c_1423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1074, c_1419])).
% 3.44/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.62  
% 3.44/1.62  Inference rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Ref     : 0
% 3.44/1.62  #Sup     : 297
% 3.44/1.62  #Fact    : 0
% 3.44/1.62  #Define  : 0
% 3.44/1.62  #Split   : 8
% 3.44/1.62  #Chain   : 0
% 3.44/1.62  #Close   : 0
% 3.44/1.62  
% 3.44/1.62  Ordering : KBO
% 3.44/1.62  
% 3.44/1.62  Simplification rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Subsume      : 11
% 3.44/1.62  #Demod        : 148
% 3.44/1.62  #Tautology    : 132
% 3.44/1.62  #SimpNegUnit  : 9
% 3.44/1.62  #BackRed      : 9
% 3.44/1.62  
% 3.44/1.62  #Partial instantiations: 0
% 3.44/1.62  #Strategies tried      : 1
% 3.44/1.62  
% 3.44/1.62  Timing (in seconds)
% 3.44/1.62  ----------------------
% 3.44/1.62  Preprocessing        : 0.33
% 3.44/1.62  Parsing              : 0.18
% 3.44/1.62  CNF conversion       : 0.02
% 3.44/1.62  Main loop            : 0.46
% 3.44/1.62  Inferencing          : 0.17
% 3.44/1.62  Reduction            : 0.13
% 3.44/1.62  Demodulation         : 0.09
% 3.44/1.62  BG Simplification    : 0.03
% 3.44/1.62  Subsumption          : 0.09
% 3.44/1.62  Abstraction          : 0.03
% 3.44/1.62  MUC search           : 0.00
% 3.44/1.62  Cooper               : 0.00
% 3.44/1.62  Total                : 0.82
% 3.44/1.62  Index Insertion      : 0.00
% 3.44/1.62  Index Deletion       : 0.00
% 3.44/1.62  Index Matching       : 0.00
% 3.44/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
