%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:18 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 878 expanded)
%              Number of leaves         :   53 ( 312 expanded)
%              Depth                    :   14
%              Number of atoms          :  298 (2599 expanded)
%              Number of equality atoms :   36 ( 416 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_169,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_30,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_28,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_132,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_8,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_4] : r1_tarski('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_48,plain,(
    ! [A_60] :
      ( v4_pre_topc(k2_struct_0(A_60),A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_88,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2])).

tff(c_30,plain,(
    ! [A_37] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,(
    ! [A_37] : m1_subset_1('#skF_4',k1_zfmisc_1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_30])).

tff(c_46,plain,(
    ! [A_59] :
      ( l1_struct_0(A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_122,plain,(
    ! [A_85] :
      ( u1_struct_0(A_85) = k2_struct_0(A_85)
      | ~ l1_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_137,plain,(
    ! [A_90] :
      ( u1_struct_0(A_90) = k2_struct_0(A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_46,c_122])).

tff(c_141,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_137])).

tff(c_76,plain,(
    ! [D_77] :
      ( r2_hidden('#skF_3',D_77)
      | ~ r2_hidden(D_77,'#skF_4')
      | ~ m1_subset_1(D_77,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_148,plain,(
    ! [D_91] :
      ( r2_hidden('#skF_3',D_91)
      | ~ r2_hidden(D_91,'#skF_4')
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_76])).

tff(c_157,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_148])).

tff(c_159,plain,(
    ~ r2_hidden('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_74,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,'#skF_4')
      | ~ r2_hidden('#skF_3',D_77)
      | ~ v4_pre_topc(D_77,'#skF_2')
      | ~ v3_pre_topc(D_77,'#skF_2')
      | ~ m1_subset_1(D_77,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_348,plain,(
    ! [D_129] :
      ( r2_hidden(D_129,'#skF_4')
      | ~ r2_hidden('#skF_3',D_129)
      | ~ v4_pre_topc(D_129,'#skF_2')
      | ~ v3_pre_topc(D_129,'#skF_2')
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_74])).

tff(c_355,plain,
    ( r2_hidden('#skF_4','#skF_4')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_348])).

tff(c_365,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_355])).

tff(c_370,plain,(
    ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_365])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_142,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_66])).

tff(c_10,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_85,plain,(
    ! [A_5] : k5_xboole_0(A_5,'#skF_4') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_87,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_6])).

tff(c_180,plain,(
    ! [A_97,B_98] : k5_xboole_0(A_97,k3_xboole_0(A_97,B_98)) = k4_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_189,plain,(
    ! [A_3] : k5_xboole_0(A_3,'#skF_4') = k4_xboole_0(A_3,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_180])).

tff(c_192,plain,(
    ! [A_3] : k4_xboole_0(A_3,'#skF_4') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_189])).

tff(c_236,plain,(
    ! [A_114,B_115] :
      ( k4_xboole_0(A_114,B_115) = k3_subset_1(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_239,plain,(
    ! [A_37] : k4_xboole_0(A_37,'#skF_4') = k3_subset_1(A_37,'#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_236])).

tff(c_244,plain,(
    ! [A_37] : k3_subset_1(A_37,'#skF_4') = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_239])).

tff(c_32,plain,(
    ! [C_44,A_38,B_42] :
      ( r2_hidden(C_44,k3_subset_1(A_38,B_42))
      | r2_hidden(C_44,B_42)
      | ~ m1_subset_1(C_44,A_38)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_38))
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_609,plain,(
    ! [C_175,A_176,B_177] :
      ( r2_hidden(C_175,k3_subset_1(A_176,B_177))
      | r2_hidden(C_175,B_177)
      | ~ m1_subset_1(C_175,A_176)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(A_176))
      | A_176 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_32])).

tff(c_618,plain,(
    ! [C_175,A_37] :
      ( r2_hidden(C_175,A_37)
      | r2_hidden(C_175,'#skF_4')
      | ~ m1_subset_1(C_175,A_37)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_37))
      | A_37 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_609])).

tff(c_639,plain,(
    ! [C_178,A_179] :
      ( r2_hidden(C_178,A_179)
      | r2_hidden(C_178,'#skF_4')
      | ~ m1_subset_1(C_178,A_179)
      | A_179 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_618])).

tff(c_24,plain,(
    ! [A_33] : k2_subset_1(A_33) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [A_36] : m1_subset_1(k2_subset_1(A_36),k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_84,plain,(
    ! [A_36] : m1_subset_1(A_36,k1_zfmisc_1(A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_158,plain,
    ( r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_148])).

tff(c_202,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_359,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),'#skF_4')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_348])).

tff(c_368,plain,
    ( ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_359])).

tff(c_429,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_371,plain,(
    ! [B_131,A_132] :
      ( v4_pre_topc(B_131,A_132)
      | ~ v1_xboole_0(B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_377,plain,(
    ! [B_131] :
      ( v4_pre_topc(B_131,'#skF_2')
      | ~ v1_xboole_0(B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_371])).

tff(c_394,plain,(
    ! [B_134] :
      ( v4_pre_topc(B_134,'#skF_2')
      | ~ v1_xboole_0(B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_377])).

tff(c_401,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_394])).

tff(c_409,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_401])).

tff(c_470,plain,(
    ! [A_148,B_149] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_148),B_149),A_148)
      | ~ v4_pre_topc(B_149,A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_477,plain,(
    ! [A_148] :
      ( v3_pre_topc(u1_struct_0(A_148),A_148)
      | ~ v4_pre_topc('#skF_4',A_148)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_470])).

tff(c_486,plain,(
    ! [A_150] :
      ( v3_pre_topc(u1_struct_0(A_150),A_150)
      | ~ v4_pre_topc('#skF_4',A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_477])).

tff(c_492,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_486])).

tff(c_495,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_409,c_492])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_429,c_495])).

tff(c_498,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_500,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_498])).

tff(c_649,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_639,c_500])).

tff(c_685,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_649])).

tff(c_697,plain,(
    k2_struct_0('#skF_2') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_685])).

tff(c_499,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_702,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_499])).

tff(c_716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_702])).

tff(c_717,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_40,plain,(
    ! [B_54,A_53] :
      ( ~ r1_tarski(B_54,A_53)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_726,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_717,c_40])).

tff(c_732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_726])).

tff(c_733,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_746,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_733])).

tff(c_750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_746])).

tff(c_751,plain,
    ( ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_775,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_751])).

tff(c_990,plain,(
    ! [C_219,A_220,B_221] :
      ( r2_hidden(C_219,k3_subset_1(A_220,B_221))
      | r2_hidden(C_219,B_221)
      | ~ m1_subset_1(C_219,A_220)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(A_220))
      | A_220 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_32])).

tff(c_999,plain,(
    ! [C_219,A_37] :
      ( r2_hidden(C_219,A_37)
      | r2_hidden(C_219,'#skF_4')
      | ~ m1_subset_1(C_219,A_37)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_37))
      | A_37 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_990])).

tff(c_1020,plain,(
    ! [C_222,A_223] :
      ( r2_hidden(C_222,A_223)
      | r2_hidden(C_222,'#skF_4')
      | ~ m1_subset_1(C_222,A_223)
      | A_223 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_999])).

tff(c_821,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_753,plain,(
    ! [B_180,A_181] :
      ( v4_pre_topc(B_180,A_181)
      | ~ v1_xboole_0(B_180)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_759,plain,(
    ! [B_180] :
      ( v4_pre_topc(B_180,'#skF_2')
      | ~ v1_xboole_0(B_180)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_753])).

tff(c_781,plain,(
    ! [B_183] :
      ( v4_pre_topc(B_183,'#skF_2')
      | ~ v1_xboole_0(B_183)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_759])).

tff(c_788,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_781])).

tff(c_796,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_788])).

tff(c_860,plain,(
    ! [A_198,B_199] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_198),B_199),A_198)
      | ~ v4_pre_topc(B_199,A_198)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_867,plain,(
    ! [A_198] :
      ( v3_pre_topc(u1_struct_0(A_198),A_198)
      | ~ v4_pre_topc('#skF_4',A_198)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_860])).

tff(c_876,plain,(
    ! [A_200] :
      ( v3_pre_topc(u1_struct_0(A_200),A_200)
      | ~ v4_pre_topc('#skF_4',A_200)
      | ~ l1_pre_topc(A_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_867])).

tff(c_882,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_876])).

tff(c_885,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_796,c_882])).

tff(c_887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_821,c_885])).

tff(c_888,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_890,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_888])).

tff(c_1030,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1020,c_890])).

tff(c_1072,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1030])).

tff(c_1073,plain,(
    k2_struct_0('#skF_2') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_775,c_1072])).

tff(c_295,plain,(
    ! [A_123] :
      ( m1_subset_1('#skF_1'(A_123),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_306,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_295])).

tff(c_311,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_306])).

tff(c_312,plain,(
    m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_311])).

tff(c_34,plain,(
    ! [B_47,A_45] :
      ( v1_xboole_0(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_45))
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_334,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_312,c_34])).

tff(c_336,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_334])).

tff(c_1094,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_336])).

tff(c_1105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1094])).

tff(c_1106,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_1119,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1106])).

tff(c_1123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1119])).

tff(c_1125,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_1133,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1125,c_40])).

tff(c_1139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1133])).

tff(c_1140,plain,(
    v1_xboole_0('#skF_1'('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_54,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0('#skF_1'(A_61))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1153,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1140,c_54])).

tff(c_1156,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1153])).

tff(c_1158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1156])).

tff(c_1160,plain,(
    r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_1167,plain,(
    ~ r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1160,c_40])).

tff(c_1171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:21:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.55  
% 3.53/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.55  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.53/1.55  
% 3.53/1.55  %Foreground sorts:
% 3.53/1.55  
% 3.53/1.55  
% 3.53/1.55  %Background operators:
% 3.53/1.55  
% 3.53/1.55  
% 3.53/1.55  %Foreground operators:
% 3.53/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.53/1.55  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.53/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.53/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.53/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.53/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.53/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.53/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.53/1.55  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.53/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.53/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.53/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.53/1.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.53/1.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.53/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.53/1.55  
% 3.74/1.57  tff(f_169, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 3.74/1.57  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.74/1.57  tff(f_115, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 3.74/1.57  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.74/1.57  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.74/1.57  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.74/1.57  tff(f_105, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.74/1.57  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.74/1.57  tff(f_30, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.74/1.57  tff(f_28, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.74/1.57  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.74/1.57  tff(f_70, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 3.74/1.57  tff(f_48, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.74/1.57  tff(f_54, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.74/1.57  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.74/1.57  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 3.74/1.57  tff(f_90, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.74/1.57  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_tops_1)).
% 3.74/1.57  tff(f_77, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.74/1.57  tff(c_62, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.74/1.57  tff(c_8, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.57  tff(c_86, plain, (![A_4]: (r1_tarski('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8])).
% 3.74/1.57  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.74/1.57  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.74/1.57  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.74/1.57  tff(c_48, plain, (![A_60]: (v4_pre_topc(k2_struct_0(A_60), A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.74/1.57  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.74/1.57  tff(c_88, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2])).
% 3.74/1.57  tff(c_30, plain, (![A_37]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.74/1.57  tff(c_82, plain, (![A_37]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_30])).
% 3.74/1.57  tff(c_46, plain, (![A_59]: (l1_struct_0(A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.74/1.57  tff(c_122, plain, (![A_85]: (u1_struct_0(A_85)=k2_struct_0(A_85) | ~l1_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.74/1.57  tff(c_137, plain, (![A_90]: (u1_struct_0(A_90)=k2_struct_0(A_90) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_46, c_122])).
% 3.74/1.57  tff(c_141, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_137])).
% 3.74/1.57  tff(c_76, plain, (![D_77]: (r2_hidden('#skF_3', D_77) | ~r2_hidden(D_77, '#skF_4') | ~m1_subset_1(D_77, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.74/1.57  tff(c_148, plain, (![D_91]: (r2_hidden('#skF_3', D_91) | ~r2_hidden(D_91, '#skF_4') | ~m1_subset_1(D_91, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_76])).
% 3.74/1.57  tff(c_157, plain, (r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_148])).
% 3.74/1.57  tff(c_159, plain, (~r2_hidden('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_157])).
% 3.74/1.57  tff(c_74, plain, (![D_77]: (r2_hidden(D_77, '#skF_4') | ~r2_hidden('#skF_3', D_77) | ~v4_pre_topc(D_77, '#skF_2') | ~v3_pre_topc(D_77, '#skF_2') | ~m1_subset_1(D_77, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.74/1.57  tff(c_348, plain, (![D_129]: (r2_hidden(D_129, '#skF_4') | ~r2_hidden('#skF_3', D_129) | ~v4_pre_topc(D_129, '#skF_2') | ~v3_pre_topc(D_129, '#skF_2') | ~m1_subset_1(D_129, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_74])).
% 3.74/1.57  tff(c_355, plain, (r2_hidden('#skF_4', '#skF_4') | ~r2_hidden('#skF_3', '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_82, c_348])).
% 3.74/1.57  tff(c_365, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_159, c_355])).
% 3.74/1.57  tff(c_370, plain, (~v3_pre_topc('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_365])).
% 3.74/1.57  tff(c_66, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.74/1.57  tff(c_142, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_66])).
% 3.74/1.57  tff(c_10, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.74/1.57  tff(c_85, plain, (![A_5]: (k5_xboole_0(A_5, '#skF_4')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10])).
% 3.74/1.57  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.74/1.57  tff(c_87, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_6])).
% 3.74/1.57  tff(c_180, plain, (![A_97, B_98]: (k5_xboole_0(A_97, k3_xboole_0(A_97, B_98))=k4_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.74/1.57  tff(c_189, plain, (![A_3]: (k5_xboole_0(A_3, '#skF_4')=k4_xboole_0(A_3, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_180])).
% 3.74/1.57  tff(c_192, plain, (![A_3]: (k4_xboole_0(A_3, '#skF_4')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_189])).
% 3.74/1.57  tff(c_236, plain, (![A_114, B_115]: (k4_xboole_0(A_114, B_115)=k3_subset_1(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.74/1.57  tff(c_239, plain, (![A_37]: (k4_xboole_0(A_37, '#skF_4')=k3_subset_1(A_37, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_236])).
% 3.74/1.57  tff(c_244, plain, (![A_37]: (k3_subset_1(A_37, '#skF_4')=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_239])).
% 3.74/1.57  tff(c_32, plain, (![C_44, A_38, B_42]: (r2_hidden(C_44, k3_subset_1(A_38, B_42)) | r2_hidden(C_44, B_42) | ~m1_subset_1(C_44, A_38) | ~m1_subset_1(B_42, k1_zfmisc_1(A_38)) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.74/1.57  tff(c_609, plain, (![C_175, A_176, B_177]: (r2_hidden(C_175, k3_subset_1(A_176, B_177)) | r2_hidden(C_175, B_177) | ~m1_subset_1(C_175, A_176) | ~m1_subset_1(B_177, k1_zfmisc_1(A_176)) | A_176='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_32])).
% 3.74/1.57  tff(c_618, plain, (![C_175, A_37]: (r2_hidden(C_175, A_37) | r2_hidden(C_175, '#skF_4') | ~m1_subset_1(C_175, A_37) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_37)) | A_37='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_244, c_609])).
% 3.74/1.57  tff(c_639, plain, (![C_178, A_179]: (r2_hidden(C_178, A_179) | r2_hidden(C_178, '#skF_4') | ~m1_subset_1(C_178, A_179) | A_179='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_618])).
% 3.74/1.57  tff(c_24, plain, (![A_33]: (k2_subset_1(A_33)=A_33)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.74/1.57  tff(c_28, plain, (![A_36]: (m1_subset_1(k2_subset_1(A_36), k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.74/1.57  tff(c_84, plain, (![A_36]: (m1_subset_1(A_36, k1_zfmisc_1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 3.74/1.57  tff(c_158, plain, (r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_84, c_148])).
% 3.74/1.57  tff(c_202, plain, (~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_158])).
% 3.74/1.57  tff(c_359, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_84, c_348])).
% 3.74/1.57  tff(c_368, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_202, c_359])).
% 3.74/1.57  tff(c_429, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_368])).
% 3.74/1.57  tff(c_371, plain, (![B_131, A_132]: (v4_pre_topc(B_131, A_132) | ~v1_xboole_0(B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.74/1.57  tff(c_377, plain, (![B_131]: (v4_pre_topc(B_131, '#skF_2') | ~v1_xboole_0(B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_371])).
% 3.74/1.57  tff(c_394, plain, (![B_134]: (v4_pre_topc(B_134, '#skF_2') | ~v1_xboole_0(B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_377])).
% 3.74/1.57  tff(c_401, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_394])).
% 3.74/1.57  tff(c_409, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_401])).
% 3.74/1.57  tff(c_470, plain, (![A_148, B_149]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_148), B_149), A_148) | ~v4_pre_topc(B_149, A_148) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.74/1.57  tff(c_477, plain, (![A_148]: (v3_pre_topc(u1_struct_0(A_148), A_148) | ~v4_pre_topc('#skF_4', A_148) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(superposition, [status(thm), theory('equality')], [c_244, c_470])).
% 3.74/1.57  tff(c_486, plain, (![A_150]: (v3_pre_topc(u1_struct_0(A_150), A_150) | ~v4_pre_topc('#skF_4', A_150) | ~l1_pre_topc(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_477])).
% 3.74/1.57  tff(c_492, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_141, c_486])).
% 3.74/1.57  tff(c_495, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_409, c_492])).
% 3.74/1.57  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_429, c_495])).
% 3.74/1.57  tff(c_498, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_368])).
% 3.74/1.57  tff(c_500, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_498])).
% 3.74/1.57  tff(c_649, plain, (r2_hidden('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_639, c_500])).
% 3.74/1.57  tff(c_685, plain, (r2_hidden('#skF_3', '#skF_4') | k2_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_649])).
% 3.74/1.57  tff(c_697, plain, (k2_struct_0('#skF_2')='#skF_4'), inference(splitLeft, [status(thm)], [c_685])).
% 3.74/1.57  tff(c_499, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_368])).
% 3.74/1.57  tff(c_702, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_697, c_499])).
% 3.74/1.57  tff(c_716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_702])).
% 3.74/1.57  tff(c_717, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_685])).
% 3.74/1.57  tff(c_40, plain, (![B_54, A_53]: (~r1_tarski(B_54, A_53) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.74/1.57  tff(c_726, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_717, c_40])).
% 3.74/1.57  tff(c_732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_726])).
% 3.74/1.57  tff(c_733, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_498])).
% 3.74/1.57  tff(c_746, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_733])).
% 3.74/1.57  tff(c_750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_746])).
% 3.74/1.57  tff(c_751, plain, (~v4_pre_topc('#skF_4', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_365])).
% 3.74/1.57  tff(c_775, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_751])).
% 3.74/1.57  tff(c_990, plain, (![C_219, A_220, B_221]: (r2_hidden(C_219, k3_subset_1(A_220, B_221)) | r2_hidden(C_219, B_221) | ~m1_subset_1(C_219, A_220) | ~m1_subset_1(B_221, k1_zfmisc_1(A_220)) | A_220='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_32])).
% 3.74/1.57  tff(c_999, plain, (![C_219, A_37]: (r2_hidden(C_219, A_37) | r2_hidden(C_219, '#skF_4') | ~m1_subset_1(C_219, A_37) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_37)) | A_37='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_244, c_990])).
% 3.74/1.57  tff(c_1020, plain, (![C_222, A_223]: (r2_hidden(C_222, A_223) | r2_hidden(C_222, '#skF_4') | ~m1_subset_1(C_222, A_223) | A_223='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_999])).
% 3.74/1.57  tff(c_821, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_368])).
% 3.74/1.57  tff(c_753, plain, (![B_180, A_181]: (v4_pre_topc(B_180, A_181) | ~v1_xboole_0(B_180) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.74/1.57  tff(c_759, plain, (![B_180]: (v4_pre_topc(B_180, '#skF_2') | ~v1_xboole_0(B_180) | ~m1_subset_1(B_180, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_753])).
% 3.74/1.57  tff(c_781, plain, (![B_183]: (v4_pre_topc(B_183, '#skF_2') | ~v1_xboole_0(B_183) | ~m1_subset_1(B_183, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_759])).
% 3.74/1.57  tff(c_788, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_781])).
% 3.74/1.57  tff(c_796, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_788])).
% 3.74/1.57  tff(c_860, plain, (![A_198, B_199]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_198), B_199), A_198) | ~v4_pre_topc(B_199, A_198) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.74/1.57  tff(c_867, plain, (![A_198]: (v3_pre_topc(u1_struct_0(A_198), A_198) | ~v4_pre_topc('#skF_4', A_198) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198))), inference(superposition, [status(thm), theory('equality')], [c_244, c_860])).
% 3.74/1.58  tff(c_876, plain, (![A_200]: (v3_pre_topc(u1_struct_0(A_200), A_200) | ~v4_pre_topc('#skF_4', A_200) | ~l1_pre_topc(A_200))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_867])).
% 3.74/1.58  tff(c_882, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_141, c_876])).
% 3.74/1.58  tff(c_885, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_796, c_882])).
% 3.74/1.58  tff(c_887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_821, c_885])).
% 3.74/1.58  tff(c_888, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_368])).
% 3.74/1.58  tff(c_890, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_888])).
% 3.74/1.58  tff(c_1030, plain, (r2_hidden('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_1020, c_890])).
% 3.74/1.58  tff(c_1072, plain, (r2_hidden('#skF_3', '#skF_4') | k2_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_1030])).
% 3.74/1.58  tff(c_1073, plain, (k2_struct_0('#skF_2')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_775, c_1072])).
% 3.74/1.58  tff(c_295, plain, (![A_123]: (m1_subset_1('#skF_1'(A_123), k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.74/1.58  tff(c_306, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_141, c_295])).
% 3.74/1.58  tff(c_311, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_306])).
% 3.74/1.58  tff(c_312, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_72, c_311])).
% 3.74/1.58  tff(c_34, plain, (![B_47, A_45]: (v1_xboole_0(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_45)) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.74/1.58  tff(c_334, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_312, c_34])).
% 3.74/1.58  tff(c_336, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_334])).
% 3.74/1.58  tff(c_1094, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_336])).
% 3.74/1.58  tff(c_1105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_1094])).
% 3.74/1.58  tff(c_1106, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_888])).
% 3.74/1.58  tff(c_1119, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1106])).
% 3.74/1.58  tff(c_1123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1119])).
% 3.74/1.58  tff(c_1125, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_751])).
% 3.74/1.58  tff(c_1133, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1125, c_40])).
% 3.74/1.58  tff(c_1139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_1133])).
% 3.74/1.58  tff(c_1140, plain, (v1_xboole_0('#skF_1'('#skF_2'))), inference(splitRight, [status(thm)], [c_334])).
% 3.74/1.58  tff(c_54, plain, (![A_61]: (~v1_xboole_0('#skF_1'(A_61)) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.74/1.58  tff(c_1153, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1140, c_54])).
% 3.74/1.58  tff(c_1156, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1153])).
% 3.74/1.58  tff(c_1158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1156])).
% 3.74/1.58  tff(c_1160, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_158])).
% 3.74/1.58  tff(c_1167, plain, (~r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1160, c_40])).
% 3.74/1.58  tff(c_1171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_1167])).
% 3.74/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.58  
% 3.74/1.58  Inference rules
% 3.74/1.58  ----------------------
% 3.74/1.58  #Ref     : 0
% 3.74/1.58  #Sup     : 187
% 3.74/1.58  #Fact    : 4
% 3.74/1.58  #Define  : 0
% 3.74/1.58  #Split   : 22
% 3.74/1.58  #Chain   : 0
% 3.74/1.58  #Close   : 0
% 3.74/1.58  
% 3.74/1.58  Ordering : KBO
% 3.74/1.58  
% 3.74/1.58  Simplification rules
% 3.74/1.58  ----------------------
% 3.74/1.58  #Subsume      : 18
% 3.74/1.58  #Demod        : 170
% 3.74/1.58  #Tautology    : 82
% 3.74/1.58  #SimpNegUnit  : 18
% 3.74/1.58  #BackRed      : 33
% 3.74/1.58  
% 3.74/1.58  #Partial instantiations: 0
% 3.74/1.58  #Strategies tried      : 1
% 3.74/1.58  
% 3.74/1.58  Timing (in seconds)
% 3.74/1.58  ----------------------
% 3.74/1.58  Preprocessing        : 0.36
% 3.74/1.58  Parsing              : 0.19
% 3.74/1.58  CNF conversion       : 0.03
% 3.74/1.58  Main loop            : 0.44
% 3.74/1.58  Inferencing          : 0.16
% 3.74/1.58  Reduction            : 0.14
% 3.74/1.58  Demodulation         : 0.10
% 3.74/1.58  BG Simplification    : 0.02
% 3.74/1.58  Subsumption          : 0.07
% 3.74/1.58  Abstraction          : 0.02
% 3.74/1.58  MUC search           : 0.00
% 3.74/1.58  Cooper               : 0.00
% 3.74/1.58  Total                : 0.85
% 3.74/1.58  Index Insertion      : 0.00
% 3.74/1.58  Index Deletion       : 0.00
% 3.74/1.58  Index Matching       : 0.00
% 3.74/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
