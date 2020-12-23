%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:24 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 8.24s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 171 expanded)
%              Number of leaves         :   39 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 311 expanded)
%              Number of equality atoms :   57 ( 101 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_86,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6070,plain,(
    ! [A_255,B_256,C_257] :
      ( k7_subset_1(A_255,B_256,C_257) = k4_xboole_0(B_256,C_257)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(A_255)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6076,plain,(
    ! [C_257] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_257) = k4_xboole_0('#skF_2',C_257) ),
    inference(resolution,[status(thm)],[c_44,c_6070])).

tff(c_50,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_136,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1226,plain,(
    ! [B_129,A_130] :
      ( v4_pre_topc(B_129,A_130)
      | k2_pre_topc(A_130,B_129) != B_129
      | ~ v2_pre_topc(A_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1233,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1226])).

tff(c_1237,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_1233])).

tff(c_1238,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_1237])).

tff(c_1575,plain,(
    ! [A_141,B_142] :
      ( k4_subset_1(u1_struct_0(A_141),B_142,k2_tops_1(A_141,B_142)) = k2_pre_topc(A_141,B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1580,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1575])).

tff(c_1584,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1580])).

tff(c_56,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_205,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_56])).

tff(c_527,plain,(
    ! [A_87,B_88,C_89] :
      ( k7_subset_1(A_87,B_88,C_89) = k4_xboole_0(B_88,C_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_570,plain,(
    ! [C_92] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_92) = k4_xboole_0('#skF_2',C_92) ),
    inference(resolution,[status(thm)],[c_44,c_527])).

tff(c_582,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_570])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_137,plain,(
    ! [A_54,B_55] :
      ( k2_xboole_0(A_54,B_55) = B_55
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    ! [A_57,B_58] : k2_xboole_0(k4_xboole_0(A_57,B_58),A_57) = A_57 ),
    inference(resolution,[status(thm)],[c_20,c_137])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_168,plain,(
    ! [A_57,B_58] : k2_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_2])).

tff(c_720,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_168])).

tff(c_127,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_135,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_127])).

tff(c_212,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_222,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_135,c_212])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_382,plain,(
    ! [A_77,C_78,B_79] :
      ( r1_tarski(A_77,C_78)
      | ~ r1_tarski(B_79,C_78)
      | ~ r1_tarski(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_680,plain,(
    ! [A_97,A_98,B_99] :
      ( r1_tarski(A_97,A_98)
      | ~ r1_tarski(A_97,k4_xboole_0(A_98,B_99)) ) ),
    inference(resolution,[status(thm)],[c_20,c_382])).

tff(c_770,plain,(
    ! [A_100,B_101,B_102] : r1_tarski(k4_xboole_0(k4_xboole_0(A_100,B_101),B_102),A_100) ),
    inference(resolution,[status(thm)],[c_20,c_680])).

tff(c_859,plain,(
    ! [A_109,B_110,B_111] : r1_tarski(k4_xboole_0(k3_xboole_0(A_109,B_110),B_111),A_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_770])).

tff(c_1079,plain,(
    ! [B_123,A_124,B_125] : r1_tarski(k4_xboole_0(k3_xboole_0(B_123,A_124),B_125),A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_859])).

tff(c_1122,plain,(
    ! [B_126] : r1_tarski(k4_xboole_0('#skF_2',B_126),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_1079])).

tff(c_1134,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_1122])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_804,plain,(
    ! [A_103,B_104,C_105] :
      ( k4_subset_1(A_103,B_104,C_105) = k2_xboole_0(B_104,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5366,plain,(
    ! [B_212,B_213,A_214] :
      ( k4_subset_1(B_212,B_213,A_214) = k2_xboole_0(B_213,A_214)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(B_212))
      | ~ r1_tarski(A_214,B_212) ) ),
    inference(resolution,[status(thm)],[c_32,c_804])).

tff(c_5593,plain,(
    ! [A_221] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_221) = k2_xboole_0('#skF_2',A_221)
      | ~ r1_tarski(A_221,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_44,c_5366])).

tff(c_5618,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1134,c_5593])).

tff(c_5680,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_720,c_5618])).

tff(c_5682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1238,c_5680])).

tff(c_5683,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6080,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6076,c_5683])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5756,plain,(
    ! [A_231,B_232] :
      ( k3_xboole_0(A_231,B_232) = A_231
      | ~ r1_tarski(A_231,B_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5768,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_5756])).

tff(c_5684,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6378,plain,(
    ! [A_277,B_278] :
      ( r1_tarski(k2_tops_1(A_277,B_278),B_278)
      | ~ v4_pre_topc(B_278,A_277)
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ l1_pre_topc(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6383,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_6378])).

tff(c_6387,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5684,c_6383])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6400,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6387,c_18])).

tff(c_5843,plain,(
    ! [A_239,B_240] : k4_xboole_0(A_239,k4_xboole_0(A_239,B_240)) = k3_xboole_0(A_239,B_240) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5871,plain,(
    ! [A_241,B_242] : r1_tarski(k3_xboole_0(A_241,B_242),A_241) ),
    inference(superposition,[status(thm),theory(equality)],[c_5843,c_20])).

tff(c_8087,plain,(
    ! [A_334,B_335] : k3_xboole_0(k3_xboole_0(A_334,B_335),A_334) = k3_xboole_0(A_334,B_335) ),
    inference(resolution,[status(thm)],[c_5871,c_18])).

tff(c_8192,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6400,c_8087])).

tff(c_8251,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5768,c_4,c_8192])).

tff(c_7130,plain,(
    ! [A_313,B_314] :
      ( k7_subset_1(u1_struct_0(A_313),B_314,k2_tops_1(A_313,B_314)) = k1_tops_1(A_313,B_314)
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ l1_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_7135,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_7130])).

tff(c_7139,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6076,c_7135])).

tff(c_7161,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7139,c_22])).

tff(c_13916,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8251,c_7161])).

tff(c_13917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6080,c_13916])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:50:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.97/2.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.24/2.81  
% 8.24/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.24/2.81  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 8.24/2.81  
% 8.24/2.81  %Foreground sorts:
% 8.24/2.81  
% 8.24/2.81  
% 8.24/2.81  %Background operators:
% 8.24/2.81  
% 8.24/2.81  
% 8.24/2.81  %Foreground operators:
% 8.24/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.24/2.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.24/2.81  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.24/2.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.24/2.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.24/2.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.24/2.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.24/2.81  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.24/2.81  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.24/2.81  tff('#skF_2', type, '#skF_2': $i).
% 8.24/2.81  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.24/2.81  tff('#skF_1', type, '#skF_1': $i).
% 8.24/2.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.24/2.81  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.24/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.24/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.24/2.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.24/2.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.24/2.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.24/2.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.24/2.81  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.24/2.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.24/2.81  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.24/2.81  
% 8.24/2.83  tff(f_121, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 8.24/2.83  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.24/2.83  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.24/2.83  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 8.24/2.83  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.24/2.83  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.24/2.83  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.24/2.83  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.24/2.83  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.24/2.83  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.24/2.83  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.24/2.83  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.24/2.83  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.24/2.83  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.24/2.83  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 8.24/2.83  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 8.24/2.83  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.24/2.83  tff(c_6070, plain, (![A_255, B_256, C_257]: (k7_subset_1(A_255, B_256, C_257)=k4_xboole_0(B_256, C_257) | ~m1_subset_1(B_256, k1_zfmisc_1(A_255)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.24/2.83  tff(c_6076, plain, (![C_257]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_257)=k4_xboole_0('#skF_2', C_257))), inference(resolution, [status(thm)], [c_44, c_6070])).
% 8.24/2.83  tff(c_50, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.24/2.83  tff(c_136, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 8.24/2.83  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.24/2.83  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.24/2.83  tff(c_1226, plain, (![B_129, A_130]: (v4_pre_topc(B_129, A_130) | k2_pre_topc(A_130, B_129)!=B_129 | ~v2_pre_topc(A_130) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.24/2.83  tff(c_1233, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1226])).
% 8.24/2.83  tff(c_1237, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_1233])).
% 8.24/2.83  tff(c_1238, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_136, c_1237])).
% 8.24/2.83  tff(c_1575, plain, (![A_141, B_142]: (k4_subset_1(u1_struct_0(A_141), B_142, k2_tops_1(A_141, B_142))=k2_pre_topc(A_141, B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.24/2.83  tff(c_1580, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1575])).
% 8.24/2.83  tff(c_1584, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1580])).
% 8.24/2.83  tff(c_56, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.24/2.83  tff(c_205, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_136, c_56])).
% 8.24/2.83  tff(c_527, plain, (![A_87, B_88, C_89]: (k7_subset_1(A_87, B_88, C_89)=k4_xboole_0(B_88, C_89) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.24/2.83  tff(c_570, plain, (![C_92]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_92)=k4_xboole_0('#skF_2', C_92))), inference(resolution, [status(thm)], [c_44, c_527])).
% 8.24/2.83  tff(c_582, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_205, c_570])).
% 8.24/2.83  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.24/2.83  tff(c_137, plain, (![A_54, B_55]: (k2_xboole_0(A_54, B_55)=B_55 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.24/2.83  tff(c_159, plain, (![A_57, B_58]: (k2_xboole_0(k4_xboole_0(A_57, B_58), A_57)=A_57)), inference(resolution, [status(thm)], [c_20, c_137])).
% 8.24/2.83  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.24/2.83  tff(c_168, plain, (![A_57, B_58]: (k2_xboole_0(A_57, k4_xboole_0(A_57, B_58))=A_57)), inference(superposition, [status(thm), theory('equality')], [c_159, c_2])).
% 8.24/2.83  tff(c_720, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_582, c_168])).
% 8.24/2.83  tff(c_127, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.24/2.83  tff(c_135, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_127])).
% 8.24/2.83  tff(c_212, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.24/2.83  tff(c_222, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_135, c_212])).
% 8.24/2.83  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.24/2.83  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.24/2.83  tff(c_382, plain, (![A_77, C_78, B_79]: (r1_tarski(A_77, C_78) | ~r1_tarski(B_79, C_78) | ~r1_tarski(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.24/2.83  tff(c_680, plain, (![A_97, A_98, B_99]: (r1_tarski(A_97, A_98) | ~r1_tarski(A_97, k4_xboole_0(A_98, B_99)))), inference(resolution, [status(thm)], [c_20, c_382])).
% 8.24/2.83  tff(c_770, plain, (![A_100, B_101, B_102]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_100, B_101), B_102), A_100))), inference(resolution, [status(thm)], [c_20, c_680])).
% 8.24/2.83  tff(c_859, plain, (![A_109, B_110, B_111]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_109, B_110), B_111), A_109))), inference(superposition, [status(thm), theory('equality')], [c_22, c_770])).
% 8.24/2.83  tff(c_1079, plain, (![B_123, A_124, B_125]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_123, A_124), B_125), A_124))), inference(superposition, [status(thm), theory('equality')], [c_4, c_859])).
% 8.24/2.83  tff(c_1122, plain, (![B_126]: (r1_tarski(k4_xboole_0('#skF_2', B_126), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_222, c_1079])).
% 8.24/2.83  tff(c_1134, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_582, c_1122])).
% 8.24/2.83  tff(c_32, plain, (![A_28, B_29]: (m1_subset_1(A_28, k1_zfmisc_1(B_29)) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.24/2.83  tff(c_804, plain, (![A_103, B_104, C_105]: (k4_subset_1(A_103, B_104, C_105)=k2_xboole_0(B_104, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.24/2.83  tff(c_5366, plain, (![B_212, B_213, A_214]: (k4_subset_1(B_212, B_213, A_214)=k2_xboole_0(B_213, A_214) | ~m1_subset_1(B_213, k1_zfmisc_1(B_212)) | ~r1_tarski(A_214, B_212))), inference(resolution, [status(thm)], [c_32, c_804])).
% 8.24/2.83  tff(c_5593, plain, (![A_221]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_221)=k2_xboole_0('#skF_2', A_221) | ~r1_tarski(A_221, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_44, c_5366])).
% 8.24/2.83  tff(c_5618, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1134, c_5593])).
% 8.24/2.83  tff(c_5680, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_720, c_5618])).
% 8.24/2.83  tff(c_5682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1238, c_5680])).
% 8.24/2.83  tff(c_5683, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 8.24/2.83  tff(c_6080, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6076, c_5683])).
% 8.24/2.83  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.24/2.83  tff(c_5756, plain, (![A_231, B_232]: (k3_xboole_0(A_231, B_232)=A_231 | ~r1_tarski(A_231, B_232))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.24/2.83  tff(c_5768, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_5756])).
% 8.24/2.83  tff(c_5684, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 8.24/2.83  tff(c_6378, plain, (![A_277, B_278]: (r1_tarski(k2_tops_1(A_277, B_278), B_278) | ~v4_pre_topc(B_278, A_277) | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0(A_277))) | ~l1_pre_topc(A_277))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.24/2.83  tff(c_6383, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_6378])).
% 8.24/2.83  tff(c_6387, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5684, c_6383])).
% 8.24/2.83  tff(c_18, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.24/2.83  tff(c_6400, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6387, c_18])).
% 8.24/2.83  tff(c_5843, plain, (![A_239, B_240]: (k4_xboole_0(A_239, k4_xboole_0(A_239, B_240))=k3_xboole_0(A_239, B_240))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.24/2.83  tff(c_5871, plain, (![A_241, B_242]: (r1_tarski(k3_xboole_0(A_241, B_242), A_241))), inference(superposition, [status(thm), theory('equality')], [c_5843, c_20])).
% 8.24/2.83  tff(c_8087, plain, (![A_334, B_335]: (k3_xboole_0(k3_xboole_0(A_334, B_335), A_334)=k3_xboole_0(A_334, B_335))), inference(resolution, [status(thm)], [c_5871, c_18])).
% 8.24/2.83  tff(c_8192, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6400, c_8087])).
% 8.24/2.83  tff(c_8251, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5768, c_4, c_8192])).
% 8.24/2.83  tff(c_7130, plain, (![A_313, B_314]: (k7_subset_1(u1_struct_0(A_313), B_314, k2_tops_1(A_313, B_314))=k1_tops_1(A_313, B_314) | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0(A_313))) | ~l1_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.24/2.83  tff(c_7135, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_7130])).
% 8.24/2.83  tff(c_7139, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6076, c_7135])).
% 8.24/2.83  tff(c_7161, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7139, c_22])).
% 8.24/2.83  tff(c_13916, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8251, c_7161])).
% 8.24/2.83  tff(c_13917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6080, c_13916])).
% 8.24/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.24/2.83  
% 8.24/2.83  Inference rules
% 8.24/2.83  ----------------------
% 8.24/2.83  #Ref     : 0
% 8.24/2.83  #Sup     : 3357
% 8.24/2.83  #Fact    : 0
% 8.24/2.83  #Define  : 0
% 8.24/2.83  #Split   : 5
% 8.24/2.83  #Chain   : 0
% 8.24/2.83  #Close   : 0
% 8.24/2.83  
% 8.24/2.83  Ordering : KBO
% 8.24/2.83  
% 8.24/2.83  Simplification rules
% 8.24/2.83  ----------------------
% 8.24/2.83  #Subsume      : 159
% 8.24/2.83  #Demod        : 2383
% 8.24/2.83  #Tautology    : 2110
% 8.24/2.83  #SimpNegUnit  : 5
% 8.24/2.83  #BackRed      : 1
% 8.24/2.83  
% 8.24/2.83  #Partial instantiations: 0
% 8.24/2.83  #Strategies tried      : 1
% 8.24/2.83  
% 8.24/2.83  Timing (in seconds)
% 8.24/2.83  ----------------------
% 8.24/2.83  Preprocessing        : 0.35
% 8.24/2.83  Parsing              : 0.18
% 8.24/2.83  CNF conversion       : 0.02
% 8.24/2.83  Main loop            : 1.66
% 8.24/2.83  Inferencing          : 0.46
% 8.24/2.83  Reduction            : 0.76
% 8.24/2.83  Demodulation         : 0.63
% 8.24/2.83  BG Simplification    : 0.05
% 8.24/2.83  Subsumption          : 0.28
% 8.24/2.83  Abstraction          : 0.08
% 8.24/2.83  MUC search           : 0.00
% 8.24/2.83  Cooper               : 0.00
% 8.24/2.83  Total                : 2.05
% 8.24/2.83  Index Insertion      : 0.00
% 8.24/2.83  Index Deletion       : 0.00
% 8.24/2.83  Index Matching       : 0.00
% 8.24/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
