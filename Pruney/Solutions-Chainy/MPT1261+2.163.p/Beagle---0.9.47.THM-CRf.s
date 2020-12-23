%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:35 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.96s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 284 expanded)
%              Number of leaves         :   38 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 560 expanded)
%              Number of equality atoms :   77 ( 188 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2473,plain,(
    ! [A_218,B_219,C_220] :
      ( k7_subset_1(A_218,B_219,C_220) = k4_xboole_0(B_219,C_220)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(A_218)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2489,plain,(
    ! [C_220] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_220) = k4_xboole_0('#skF_2',C_220) ),
    inference(resolution,[status(thm)],[c_38,c_2473])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_231,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_919,plain,(
    ! [A_108,B_109] :
      ( k4_subset_1(u1_struct_0(A_108),B_109,k2_tops_1(A_108,B_109)) = k2_pre_topc(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_934,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_919])).

tff(c_953,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_934])).

tff(c_14,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [B_49] : k4_xboole_0(B_49,B_49) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_18,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_110,plain,(
    ! [B_50] : r1_tarski(k1_xboole_0,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_18])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    ! [B_50] : k4_xboole_0(k1_xboole_0,B_50) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_10])).

tff(c_155,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_164,plain,(
    ! [B_50] : k5_xboole_0(B_50,k1_xboole_0) = k2_xboole_0(B_50,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_155])).

tff(c_170,plain,(
    ! [B_50] : k5_xboole_0(B_50,k1_xboole_0) = B_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_164])).

tff(c_470,plain,(
    ! [A_83,B_84,C_85] :
      ( k7_subset_1(A_83,B_84,C_85) = k4_xboole_0(B_84,C_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_477,plain,(
    ! [C_86] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_86) = k4_xboole_0('#skF_2',C_86) ),
    inference(resolution,[status(thm)],[c_38,c_470])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_86,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_483,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_86])).

tff(c_98,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_87])).

tff(c_512,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_98])).

tff(c_20,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_564,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_20])).

tff(c_577,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_564])).

tff(c_64,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [A_10,B_11] : k3_xboole_0(k4_xboole_0(A_10,B_11),A_10) = k4_xboole_0(A_10,B_11) ),
    inference(resolution,[status(thm)],[c_18,c_64])).

tff(c_506,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_75])).

tff(c_523,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_506])).

tff(c_594,plain,(
    ! [A_87,B_88,C_89] :
      ( k9_subset_1(A_87,B_88,C_89) = k3_xboole_0(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_600,plain,(
    ! [B_88] : k9_subset_1(u1_struct_0('#skF_1'),B_88,'#skF_2') = k3_xboole_0(B_88,'#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_594])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k9_subset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_731,plain,(
    ! [A_98,B_99,C_100] :
      ( k4_subset_1(A_98,B_99,C_100) = k2_xboole_0(B_99,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1755,plain,(
    ! [A_155,B_156,B_157,C_158] :
      ( k4_subset_1(A_155,B_156,k9_subset_1(A_155,B_157,C_158)) = k2_xboole_0(B_156,k9_subset_1(A_155,B_157,C_158))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(A_155)) ) ),
    inference(resolution,[status(thm)],[c_22,c_731])).

tff(c_1842,plain,(
    ! [B_163,C_164] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k9_subset_1(u1_struct_0('#skF_1'),B_163,C_164)) = k2_xboole_0('#skF_2',k9_subset_1(u1_struct_0('#skF_1'),B_163,C_164))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_1755])).

tff(c_1860,plain,(
    ! [B_88] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_xboole_0(B_88,'#skF_2')) = k2_xboole_0('#skF_2',k9_subset_1(u1_struct_0('#skF_1'),B_88,'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_1842])).

tff(c_1871,plain,(
    ! [B_165] : k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_xboole_0(B_165,'#skF_2')) = k2_xboole_0('#skF_2',k3_xboole_0(B_165,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_600,c_1860])).

tff(c_1880,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_1871])).

tff(c_1895,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_577,c_523,c_1880])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_671,plain,(
    ! [A_94,B_95] :
      ( v4_pre_topc(k2_pre_topc(A_94,B_95),A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_684,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_671])).

tff(c_700,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_684])).

tff(c_1900,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1895,c_700])).

tff(c_1902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_1900])).

tff(c_1903,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1903,c_86])).

tff(c_2106,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2132,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2106,c_44])).

tff(c_2518,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2489,c_2132])).

tff(c_3055,plain,(
    ! [A_253,B_254] :
      ( k4_subset_1(u1_struct_0(A_253),B_254,k2_tops_1(A_253,B_254)) = k2_pre_topc(A_253,B_254)
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ l1_pre_topc(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3076,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_3055])).

tff(c_3104,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3076])).

tff(c_2108,plain,(
    ! [A_183,B_184] :
      ( k4_xboole_0(A_183,B_184) = k1_xboole_0
      | ~ r1_tarski(A_183,B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2121,plain,(
    ! [B_185] : k4_xboole_0(B_185,B_185) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2108])).

tff(c_2133,plain,(
    ! [B_186] : r1_tarski(k1_xboole_0,B_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_2121,c_18])).

tff(c_2140,plain,(
    ! [B_186] : k4_xboole_0(k1_xboole_0,B_186) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2133,c_10])).

tff(c_2289,plain,(
    ! [A_198,B_199] : k5_xboole_0(A_198,k4_xboole_0(B_199,A_198)) = k2_xboole_0(A_198,B_199) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2301,plain,(
    ! [B_186] : k5_xboole_0(B_186,k1_xboole_0) = k2_xboole_0(B_186,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2140,c_2289])).

tff(c_2307,plain,(
    ! [B_186] : k5_xboole_0(B_186,k1_xboole_0) = B_186 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2301])).

tff(c_2765,plain,(
    ! [A_243,B_244] :
      ( r1_tarski(k2_tops_1(A_243,B_244),B_244)
      | ~ v4_pre_topc(B_244,A_243)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2780,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_2765])).

tff(c_2799,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2106,c_2780])).

tff(c_2813,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2799,c_10])).

tff(c_2835,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2813,c_20])).

tff(c_2850,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2307,c_2835])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2814,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2799,c_16])).

tff(c_2362,plain,(
    ! [A_204,B_205,C_206] :
      ( k9_subset_1(A_204,B_205,C_206) = k3_xboole_0(B_205,C_206)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(A_204)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2365,plain,(
    ! [B_205] : k9_subset_1(u1_struct_0('#skF_1'),B_205,'#skF_2') = k3_xboole_0(B_205,'#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_2362])).

tff(c_2897,plain,(
    ! [A_245,B_246,C_247] :
      ( k4_subset_1(A_245,B_246,C_247) = k2_xboole_0(B_246,C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(A_245))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(A_245)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3762,plain,(
    ! [A_298,B_299,B_300,C_301] :
      ( k4_subset_1(A_298,B_299,k9_subset_1(A_298,B_300,C_301)) = k2_xboole_0(B_299,k9_subset_1(A_298,B_300,C_301))
      | ~ m1_subset_1(B_299,k1_zfmisc_1(A_298))
      | ~ m1_subset_1(C_301,k1_zfmisc_1(A_298)) ) ),
    inference(resolution,[status(thm)],[c_22,c_2897])).

tff(c_3918,plain,(
    ! [B_308,C_309] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k9_subset_1(u1_struct_0('#skF_1'),B_308,C_309)) = k2_xboole_0('#skF_2',k9_subset_1(u1_struct_0('#skF_1'),B_308,C_309))
      | ~ m1_subset_1(C_309,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_3762])).

tff(c_3942,plain,(
    ! [B_205] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_xboole_0(B_205,'#skF_2')) = k2_xboole_0('#skF_2',k9_subset_1(u1_struct_0('#skF_1'),B_205,'#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2365,c_3918])).

tff(c_4017,plain,(
    ! [B_312] : k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_xboole_0(B_312,'#skF_2')) = k2_xboole_0('#skF_2',k3_xboole_0(B_312,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2365,c_3942])).

tff(c_4026,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2814,c_4017])).

tff(c_4041,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3104,c_2850,c_2814,c_4026])).

tff(c_32,plain,(
    ! [A_28,B_30] :
      ( k7_subset_1(u1_struct_0(A_28),k2_pre_topc(A_28,B_30),k1_tops_1(A_28,B_30)) = k2_tops_1(A_28,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4051,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4041,c_32])).

tff(c_4055,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2489,c_4051])).

tff(c_4057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2518,c_4055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:11:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.91  
% 4.61/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.96/1.91  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.96/1.91  
% 4.96/1.91  %Foreground sorts:
% 4.96/1.91  
% 4.96/1.91  
% 4.96/1.91  %Background operators:
% 4.96/1.91  
% 4.96/1.91  
% 4.96/1.91  %Foreground operators:
% 4.96/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.96/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.96/1.91  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.96/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.96/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.96/1.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.96/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.96/1.91  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.96/1.91  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.96/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.96/1.91  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.96/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.96/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.96/1.91  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.96/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.96/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.96/1.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.96/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.96/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.96/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.96/1.91  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.96/1.91  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.96/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.96/1.91  
% 4.96/1.93  tff(f_108, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.96/1.93  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.96/1.93  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.96/1.93  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.96/1.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.96/1.93  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.96/1.93  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.96/1.93  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.96/1.93  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.96/1.93  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.96/1.93  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 4.96/1.93  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.96/1.93  tff(f_73, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 4.96/1.93  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 4.96/1.93  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.96/1.93  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.96/1.93  tff(c_2473, plain, (![A_218, B_219, C_220]: (k7_subset_1(A_218, B_219, C_220)=k4_xboole_0(B_219, C_220) | ~m1_subset_1(B_219, k1_zfmisc_1(A_218)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.96/1.93  tff(c_2489, plain, (![C_220]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_220)=k4_xboole_0('#skF_2', C_220))), inference(resolution, [status(thm)], [c_38, c_2473])).
% 4.96/1.93  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.96/1.93  tff(c_231, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.96/1.93  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.96/1.93  tff(c_919, plain, (![A_108, B_109]: (k4_subset_1(u1_struct_0(A_108), B_109, k2_tops_1(A_108, B_109))=k2_pre_topc(A_108, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.96/1.93  tff(c_934, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_919])).
% 4.96/1.93  tff(c_953, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_934])).
% 4.96/1.93  tff(c_14, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.96/1.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.96/1.93  tff(c_87, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.96/1.93  tff(c_100, plain, (![B_49]: (k4_xboole_0(B_49, B_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_87])).
% 4.96/1.93  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.96/1.93  tff(c_110, plain, (![B_50]: (r1_tarski(k1_xboole_0, B_50))), inference(superposition, [status(thm), theory('equality')], [c_100, c_18])).
% 4.96/1.93  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.96/1.93  tff(c_117, plain, (![B_50]: (k4_xboole_0(k1_xboole_0, B_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_10])).
% 4.96/1.93  tff(c_155, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k4_xboole_0(B_54, A_53))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.96/1.93  tff(c_164, plain, (![B_50]: (k5_xboole_0(B_50, k1_xboole_0)=k2_xboole_0(B_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_117, c_155])).
% 4.96/1.93  tff(c_170, plain, (![B_50]: (k5_xboole_0(B_50, k1_xboole_0)=B_50)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_164])).
% 4.96/1.93  tff(c_470, plain, (![A_83, B_84, C_85]: (k7_subset_1(A_83, B_84, C_85)=k4_xboole_0(B_84, C_85) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.96/1.93  tff(c_477, plain, (![C_86]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_86)=k4_xboole_0('#skF_2', C_86))), inference(resolution, [status(thm)], [c_38, c_470])).
% 4.96/1.93  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.96/1.93  tff(c_86, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 4.96/1.93  tff(c_483, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_477, c_86])).
% 4.96/1.93  tff(c_98, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_87])).
% 4.96/1.93  tff(c_512, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_483, c_98])).
% 4.96/1.93  tff(c_20, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.96/1.93  tff(c_564, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_512, c_20])).
% 4.96/1.93  tff(c_577, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_564])).
% 4.96/1.93  tff(c_64, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.96/1.93  tff(c_75, plain, (![A_10, B_11]: (k3_xboole_0(k4_xboole_0(A_10, B_11), A_10)=k4_xboole_0(A_10, B_11))), inference(resolution, [status(thm)], [c_18, c_64])).
% 4.96/1.93  tff(c_506, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_483, c_75])).
% 4.96/1.93  tff(c_523, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_483, c_506])).
% 4.96/1.93  tff(c_594, plain, (![A_87, B_88, C_89]: (k9_subset_1(A_87, B_88, C_89)=k3_xboole_0(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.96/1.93  tff(c_600, plain, (![B_88]: (k9_subset_1(u1_struct_0('#skF_1'), B_88, '#skF_2')=k3_xboole_0(B_88, '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_594])).
% 4.96/1.93  tff(c_22, plain, (![A_14, B_15, C_16]: (m1_subset_1(k9_subset_1(A_14, B_15, C_16), k1_zfmisc_1(A_14)) | ~m1_subset_1(C_16, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.96/1.93  tff(c_731, plain, (![A_98, B_99, C_100]: (k4_subset_1(A_98, B_99, C_100)=k2_xboole_0(B_99, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.96/1.93  tff(c_1755, plain, (![A_155, B_156, B_157, C_158]: (k4_subset_1(A_155, B_156, k9_subset_1(A_155, B_157, C_158))=k2_xboole_0(B_156, k9_subset_1(A_155, B_157, C_158)) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)) | ~m1_subset_1(C_158, k1_zfmisc_1(A_155)))), inference(resolution, [status(thm)], [c_22, c_731])).
% 4.96/1.93  tff(c_1842, plain, (![B_163, C_164]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k9_subset_1(u1_struct_0('#skF_1'), B_163, C_164))=k2_xboole_0('#skF_2', k9_subset_1(u1_struct_0('#skF_1'), B_163, C_164)) | ~m1_subset_1(C_164, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_38, c_1755])).
% 4.96/1.93  tff(c_1860, plain, (![B_88]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_xboole_0(B_88, '#skF_2'))=k2_xboole_0('#skF_2', k9_subset_1(u1_struct_0('#skF_1'), B_88, '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_600, c_1842])).
% 4.96/1.93  tff(c_1871, plain, (![B_165]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_xboole_0(B_165, '#skF_2'))=k2_xboole_0('#skF_2', k3_xboole_0(B_165, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_600, c_1860])).
% 4.96/1.93  tff(c_1880, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_523, c_1871])).
% 4.96/1.93  tff(c_1895, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_953, c_577, c_523, c_1880])).
% 4.96/1.93  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.96/1.93  tff(c_671, plain, (![A_94, B_95]: (v4_pre_topc(k2_pre_topc(A_94, B_95), A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.96/1.93  tff(c_684, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_671])).
% 4.96/1.93  tff(c_700, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_684])).
% 4.96/1.93  tff(c_1900, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1895, c_700])).
% 4.96/1.93  tff(c_1902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_231, c_1900])).
% 4.96/1.93  tff(c_1903, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.96/1.93  tff(c_2105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1903, c_86])).
% 4.96/1.93  tff(c_2106, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.96/1.93  tff(c_2132, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2106, c_44])).
% 4.96/1.93  tff(c_2518, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2489, c_2132])).
% 4.96/1.93  tff(c_3055, plain, (![A_253, B_254]: (k4_subset_1(u1_struct_0(A_253), B_254, k2_tops_1(A_253, B_254))=k2_pre_topc(A_253, B_254) | ~m1_subset_1(B_254, k1_zfmisc_1(u1_struct_0(A_253))) | ~l1_pre_topc(A_253))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.96/1.93  tff(c_3076, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_3055])).
% 4.96/1.93  tff(c_3104, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3076])).
% 4.96/1.93  tff(c_2108, plain, (![A_183, B_184]: (k4_xboole_0(A_183, B_184)=k1_xboole_0 | ~r1_tarski(A_183, B_184))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.96/1.93  tff(c_2121, plain, (![B_185]: (k4_xboole_0(B_185, B_185)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_2108])).
% 4.96/1.93  tff(c_2133, plain, (![B_186]: (r1_tarski(k1_xboole_0, B_186))), inference(superposition, [status(thm), theory('equality')], [c_2121, c_18])).
% 4.96/1.93  tff(c_2140, plain, (![B_186]: (k4_xboole_0(k1_xboole_0, B_186)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2133, c_10])).
% 4.96/1.93  tff(c_2289, plain, (![A_198, B_199]: (k5_xboole_0(A_198, k4_xboole_0(B_199, A_198))=k2_xboole_0(A_198, B_199))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.96/1.93  tff(c_2301, plain, (![B_186]: (k5_xboole_0(B_186, k1_xboole_0)=k2_xboole_0(B_186, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2140, c_2289])).
% 4.96/1.93  tff(c_2307, plain, (![B_186]: (k5_xboole_0(B_186, k1_xboole_0)=B_186)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2301])).
% 4.96/1.93  tff(c_2765, plain, (![A_243, B_244]: (r1_tarski(k2_tops_1(A_243, B_244), B_244) | ~v4_pre_topc(B_244, A_243) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.96/1.93  tff(c_2780, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_2765])).
% 4.96/1.93  tff(c_2799, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2106, c_2780])).
% 4.96/1.93  tff(c_2813, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2799, c_10])).
% 4.96/1.93  tff(c_2835, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2813, c_20])).
% 4.96/1.93  tff(c_2850, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2307, c_2835])).
% 4.96/1.93  tff(c_16, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.96/1.93  tff(c_2814, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2799, c_16])).
% 4.96/1.93  tff(c_2362, plain, (![A_204, B_205, C_206]: (k9_subset_1(A_204, B_205, C_206)=k3_xboole_0(B_205, C_206) | ~m1_subset_1(C_206, k1_zfmisc_1(A_204)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.96/1.93  tff(c_2365, plain, (![B_205]: (k9_subset_1(u1_struct_0('#skF_1'), B_205, '#skF_2')=k3_xboole_0(B_205, '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_2362])).
% 4.96/1.93  tff(c_2897, plain, (![A_245, B_246, C_247]: (k4_subset_1(A_245, B_246, C_247)=k2_xboole_0(B_246, C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(A_245)) | ~m1_subset_1(B_246, k1_zfmisc_1(A_245)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.96/1.93  tff(c_3762, plain, (![A_298, B_299, B_300, C_301]: (k4_subset_1(A_298, B_299, k9_subset_1(A_298, B_300, C_301))=k2_xboole_0(B_299, k9_subset_1(A_298, B_300, C_301)) | ~m1_subset_1(B_299, k1_zfmisc_1(A_298)) | ~m1_subset_1(C_301, k1_zfmisc_1(A_298)))), inference(resolution, [status(thm)], [c_22, c_2897])).
% 4.96/1.93  tff(c_3918, plain, (![B_308, C_309]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k9_subset_1(u1_struct_0('#skF_1'), B_308, C_309))=k2_xboole_0('#skF_2', k9_subset_1(u1_struct_0('#skF_1'), B_308, C_309)) | ~m1_subset_1(C_309, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_38, c_3762])).
% 4.96/1.93  tff(c_3942, plain, (![B_205]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_xboole_0(B_205, '#skF_2'))=k2_xboole_0('#skF_2', k9_subset_1(u1_struct_0('#skF_1'), B_205, '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2365, c_3918])).
% 4.96/1.93  tff(c_4017, plain, (![B_312]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_xboole_0(B_312, '#skF_2'))=k2_xboole_0('#skF_2', k3_xboole_0(B_312, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2365, c_3942])).
% 4.96/1.93  tff(c_4026, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2814, c_4017])).
% 4.96/1.93  tff(c_4041, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3104, c_2850, c_2814, c_4026])).
% 4.96/1.93  tff(c_32, plain, (![A_28, B_30]: (k7_subset_1(u1_struct_0(A_28), k2_pre_topc(A_28, B_30), k1_tops_1(A_28, B_30))=k2_tops_1(A_28, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.96/1.93  tff(c_4051, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4041, c_32])).
% 4.96/1.93  tff(c_4055, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2489, c_4051])).
% 4.96/1.93  tff(c_4057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2518, c_4055])).
% 4.96/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.96/1.93  
% 4.96/1.93  Inference rules
% 4.96/1.93  ----------------------
% 4.96/1.93  #Ref     : 0
% 4.96/1.93  #Sup     : 953
% 4.96/1.93  #Fact    : 0
% 4.96/1.93  #Define  : 0
% 4.96/1.93  #Split   : 7
% 4.96/1.93  #Chain   : 0
% 4.96/1.93  #Close   : 0
% 4.96/1.93  
% 4.96/1.93  Ordering : KBO
% 4.96/1.93  
% 4.96/1.93  Simplification rules
% 4.96/1.93  ----------------------
% 4.96/1.93  #Subsume      : 31
% 4.96/1.93  #Demod        : 681
% 4.96/1.93  #Tautology    : 516
% 4.96/1.93  #SimpNegUnit  : 3
% 4.96/1.93  #BackRed      : 5
% 4.96/1.93  
% 4.96/1.93  #Partial instantiations: 0
% 4.96/1.93  #Strategies tried      : 1
% 4.96/1.93  
% 4.96/1.93  Timing (in seconds)
% 4.96/1.93  ----------------------
% 4.96/1.94  Preprocessing        : 0.32
% 4.96/1.94  Parsing              : 0.17
% 4.96/1.94  CNF conversion       : 0.02
% 4.96/1.94  Main loop            : 0.84
% 4.96/1.94  Inferencing          : 0.29
% 4.96/1.94  Reduction            : 0.32
% 4.96/1.94  Demodulation         : 0.24
% 4.96/1.94  BG Simplification    : 0.04
% 4.96/1.94  Subsumption          : 0.13
% 4.96/1.94  Abstraction          : 0.05
% 4.96/1.94  MUC search           : 0.00
% 4.96/1.94  Cooper               : 0.00
% 4.96/1.94  Total                : 1.21
% 4.96/1.94  Index Insertion      : 0.00
% 4.96/1.94  Index Deletion       : 0.00
% 4.96/1.94  Index Matching       : 0.00
% 4.96/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
