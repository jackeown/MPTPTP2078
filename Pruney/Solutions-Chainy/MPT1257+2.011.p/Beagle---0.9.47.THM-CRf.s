%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:58 EST 2020

% Result     : Theorem 9.76s
% Output     : CNFRefutation 9.91s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 140 expanded)
%              Number of leaves         :   33 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  120 ( 253 expanded)
%              Number of equality atoms :   27 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_38,plain,(
    ~ r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_77,plain,(
    ! [A_66,B_67,C_68] :
      ( k7_subset_1(A_66,B_67,C_68) = k4_xboole_0(B_67,C_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_83,plain,(
    ! [C_68] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_68) = k4_xboole_0('#skF_2',C_68) ),
    inference(resolution,[status(thm)],[c_40,c_77])).

tff(c_32,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k2_tops_1(A_43,B_44),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1390,plain,(
    ! [A_164,B_165,C_166] :
      ( k4_subset_1(A_164,k3_subset_1(A_164,B_165),C_166) = k3_subset_1(A_164,k7_subset_1(A_164,B_165,C_166))
      | ~ m1_subset_1(C_166,k1_zfmisc_1(A_164))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(A_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8522,plain,(
    ! [A_371,B_372,B_373] :
      ( k4_subset_1(u1_struct_0(A_371),k3_subset_1(u1_struct_0(A_371),B_372),k2_tops_1(A_371,B_373)) = k3_subset_1(u1_struct_0(A_371),k7_subset_1(u1_struct_0(A_371),B_372,k2_tops_1(A_371,B_373)))
      | ~ m1_subset_1(B_372,k1_zfmisc_1(u1_struct_0(A_371)))
      | ~ m1_subset_1(B_373,k1_zfmisc_1(u1_struct_0(A_371)))
      | ~ l1_pre_topc(A_371) ) ),
    inference(resolution,[status(thm)],[c_32,c_1390])).

tff(c_300,plain,(
    ! [A_97,B_98] :
      ( k2_tops_1(A_97,k3_subset_1(u1_struct_0(A_97),B_98)) = k2_tops_1(A_97,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_320,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_300])).

tff(c_337,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_320])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k3_subset_1(A_4,B_5),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_341,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_32])).

tff(c_345,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_341])).

tff(c_361,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_365,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_361])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_365])).

tff(c_371,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_444,plain,(
    ! [A_102,B_103] :
      ( k4_subset_1(u1_struct_0(A_102),B_103,k2_tops_1(A_102,B_103)) = k2_pre_topc(A_102,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_448,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_371,c_444])).

tff(c_476,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_337,c_448])).

tff(c_8532,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8522,c_476])).

tff(c_8699,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_40,c_83,c_8532])).

tff(c_93,plain,(
    ! [A_70,B_71,C_72] :
      ( m1_subset_1(k7_subset_1(A_70,B_71,C_72),k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_102,plain,(
    ! [C_68] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_68),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_93])).

tff(c_108,plain,(
    ! [C_73] : m1_subset_1(k4_xboole_0('#skF_2',C_73),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_102])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k3_subset_1(A_12,k3_subset_1(A_12,B_13)) = B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_116,plain,(
    ! [C_73] : k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2',C_73))) = k4_xboole_0('#skF_2',C_73) ),
    inference(resolution,[status(thm)],[c_108,c_12])).

tff(c_8856,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8699,c_116])).

tff(c_28,plain,(
    ! [A_38,B_40] :
      ( k3_subset_1(u1_struct_0(A_38),k2_pre_topc(A_38,k3_subset_1(u1_struct_0(A_38),B_40))) = k1_tops_1(A_38,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_9117,plain,
    ( k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8856,c_28])).

tff(c_9181,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_9117])).

tff(c_107,plain,(
    ! [C_68] : m1_subset_1(k4_xboole_0('#skF_2',C_68),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_102])).

tff(c_45,plain,(
    ! [A_58,B_59,C_60] :
      ( k9_subset_1(A_58,B_59,B_59) = B_59
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [B_59] : k9_subset_1(u1_struct_0('#skF_1'),B_59,B_59) = B_59 ),
    inference(resolution,[status(thm)],[c_40,c_45])).

tff(c_1002,plain,(
    ! [A_137,B_138,C_139] :
      ( r1_tarski(k3_subset_1(A_137,B_138),k3_subset_1(A_137,k9_subset_1(A_137,B_138,C_139)))
      | ~ m1_subset_1(C_139,k1_zfmisc_1(A_137))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1082,plain,(
    ! [B_144] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),B_144),k3_subset_1(u1_struct_0('#skF_1'),B_144))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1002])).

tff(c_16,plain,(
    ! [B_18,C_20,A_17] :
      ( r1_tarski(B_18,C_20)
      | ~ r1_tarski(k3_subset_1(A_17,C_20),k3_subset_1(A_17,B_18))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1157,plain,(
    ! [B_145] :
      ( r1_tarski(B_145,B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_1082,c_16])).

tff(c_1213,plain,(
    ! [C_146] : r1_tarski(k4_xboole_0('#skF_2',C_146),k4_xboole_0('#skF_2',C_146)) ),
    inference(resolution,[status(thm)],[c_107,c_1157])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1220,plain,(
    ! [C_146] : r1_xboole_0(k4_xboole_0('#skF_2',C_146),C_146) ),
    inference(resolution,[status(thm)],[c_1213,c_2])).

tff(c_9274,plain,(
    r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9181,c_1220])).

tff(c_9339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_9274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:43:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.76/3.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.80/3.71  
% 9.80/3.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.80/3.71  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 9.80/3.71  
% 9.80/3.71  %Foreground sorts:
% 9.80/3.71  
% 9.80/3.71  
% 9.80/3.71  %Background operators:
% 9.80/3.71  
% 9.80/3.71  
% 9.80/3.71  %Foreground operators:
% 9.80/3.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.80/3.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.80/3.71  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 9.80/3.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.80/3.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.80/3.71  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.80/3.71  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.80/3.71  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.80/3.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.80/3.71  tff('#skF_2', type, '#skF_2': $i).
% 9.80/3.71  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.80/3.71  tff('#skF_1', type, '#skF_1': $i).
% 9.80/3.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.80/3.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.80/3.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.80/3.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.80/3.71  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.80/3.71  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.80/3.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.80/3.71  
% 9.80/3.73  tff(f_133, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_1)).
% 9.80/3.73  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.80/3.73  tff(f_111, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 9.80/3.73  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k3_subset_1(A, k7_subset_1(A, B, C)) = k4_subset_1(A, k3_subset_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_subset_1)).
% 9.80/3.73  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 9.80/3.73  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.80/3.73  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 9.80/3.73  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 9.80/3.73  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.80/3.73  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 9.80/3.73  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 9.80/3.73  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 9.80/3.73  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 9.80/3.73  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 9.80/3.73  tff(c_38, plain, (~r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.80/3.73  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.80/3.73  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.80/3.73  tff(c_77, plain, (![A_66, B_67, C_68]: (k7_subset_1(A_66, B_67, C_68)=k4_xboole_0(B_67, C_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.80/3.73  tff(c_83, plain, (![C_68]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_68)=k4_xboole_0('#skF_2', C_68))), inference(resolution, [status(thm)], [c_40, c_77])).
% 9.80/3.73  tff(c_32, plain, (![A_43, B_44]: (m1_subset_1(k2_tops_1(A_43, B_44), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.80/3.73  tff(c_1390, plain, (![A_164, B_165, C_166]: (k4_subset_1(A_164, k3_subset_1(A_164, B_165), C_166)=k3_subset_1(A_164, k7_subset_1(A_164, B_165, C_166)) | ~m1_subset_1(C_166, k1_zfmisc_1(A_164)) | ~m1_subset_1(B_165, k1_zfmisc_1(A_164)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.80/3.73  tff(c_8522, plain, (![A_371, B_372, B_373]: (k4_subset_1(u1_struct_0(A_371), k3_subset_1(u1_struct_0(A_371), B_372), k2_tops_1(A_371, B_373))=k3_subset_1(u1_struct_0(A_371), k7_subset_1(u1_struct_0(A_371), B_372, k2_tops_1(A_371, B_373))) | ~m1_subset_1(B_372, k1_zfmisc_1(u1_struct_0(A_371))) | ~m1_subset_1(B_373, k1_zfmisc_1(u1_struct_0(A_371))) | ~l1_pre_topc(A_371))), inference(resolution, [status(thm)], [c_32, c_1390])).
% 9.80/3.73  tff(c_300, plain, (![A_97, B_98]: (k2_tops_1(A_97, k3_subset_1(u1_struct_0(A_97), B_98))=k2_tops_1(A_97, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.80/3.73  tff(c_320, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_300])).
% 9.80/3.73  tff(c_337, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_320])).
% 9.80/3.73  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(k3_subset_1(A_4, B_5), k1_zfmisc_1(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.80/3.73  tff(c_341, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_337, c_32])).
% 9.80/3.73  tff(c_345, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_341])).
% 9.80/3.73  tff(c_361, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_345])).
% 9.80/3.73  tff(c_365, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_361])).
% 9.80/3.73  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_365])).
% 9.80/3.73  tff(c_371, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_345])).
% 9.80/3.73  tff(c_444, plain, (![A_102, B_103]: (k4_subset_1(u1_struct_0(A_102), B_103, k2_tops_1(A_102, B_103))=k2_pre_topc(A_102, B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.80/3.73  tff(c_448, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_371, c_444])).
% 9.80/3.73  tff(c_476, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_337, c_448])).
% 9.80/3.73  tff(c_8532, plain, (k3_subset_1(u1_struct_0('#skF_1'), k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8522, c_476])).
% 9.80/3.73  tff(c_8699, plain, (k3_subset_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_40, c_83, c_8532])).
% 9.80/3.73  tff(c_93, plain, (![A_70, B_71, C_72]: (m1_subset_1(k7_subset_1(A_70, B_71, C_72), k1_zfmisc_1(A_70)) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.80/3.73  tff(c_102, plain, (![C_68]: (m1_subset_1(k4_xboole_0('#skF_2', C_68), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_83, c_93])).
% 9.80/3.73  tff(c_108, plain, (![C_73]: (m1_subset_1(k4_xboole_0('#skF_2', C_73), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_102])).
% 9.80/3.73  tff(c_12, plain, (![A_12, B_13]: (k3_subset_1(A_12, k3_subset_1(A_12, B_13))=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.80/3.73  tff(c_116, plain, (![C_73]: (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', C_73)))=k4_xboole_0('#skF_2', C_73))), inference(resolution, [status(thm)], [c_108, c_12])).
% 9.91/3.73  tff(c_8856, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8699, c_116])).
% 9.91/3.73  tff(c_28, plain, (![A_38, B_40]: (k3_subset_1(u1_struct_0(A_38), k2_pre_topc(A_38, k3_subset_1(u1_struct_0(A_38), B_40)))=k1_tops_1(A_38, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.91/3.73  tff(c_9117, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8856, c_28])).
% 9.91/3.73  tff(c_9181, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_9117])).
% 9.91/3.73  tff(c_107, plain, (![C_68]: (m1_subset_1(k4_xboole_0('#skF_2', C_68), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_102])).
% 9.91/3.73  tff(c_45, plain, (![A_58, B_59, C_60]: (k9_subset_1(A_58, B_59, B_59)=B_59 | ~m1_subset_1(C_60, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.91/3.73  tff(c_48, plain, (![B_59]: (k9_subset_1(u1_struct_0('#skF_1'), B_59, B_59)=B_59)), inference(resolution, [status(thm)], [c_40, c_45])).
% 9.91/3.73  tff(c_1002, plain, (![A_137, B_138, C_139]: (r1_tarski(k3_subset_1(A_137, B_138), k3_subset_1(A_137, k9_subset_1(A_137, B_138, C_139))) | ~m1_subset_1(C_139, k1_zfmisc_1(A_137)) | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.91/3.73  tff(c_1082, plain, (![B_144]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), B_144), k3_subset_1(u1_struct_0('#skF_1'), B_144)) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1002])).
% 9.91/3.73  tff(c_16, plain, (![B_18, C_20, A_17]: (r1_tarski(B_18, C_20) | ~r1_tarski(k3_subset_1(A_17, C_20), k3_subset_1(A_17, B_18)) | ~m1_subset_1(C_20, k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.91/3.73  tff(c_1157, plain, (![B_145]: (r1_tarski(B_145, B_145) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_1082, c_16])).
% 9.91/3.73  tff(c_1213, plain, (![C_146]: (r1_tarski(k4_xboole_0('#skF_2', C_146), k4_xboole_0('#skF_2', C_146)))), inference(resolution, [status(thm)], [c_107, c_1157])).
% 9.91/3.73  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.91/3.73  tff(c_1220, plain, (![C_146]: (r1_xboole_0(k4_xboole_0('#skF_2', C_146), C_146))), inference(resolution, [status(thm)], [c_1213, c_2])).
% 9.91/3.73  tff(c_9274, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9181, c_1220])).
% 9.91/3.73  tff(c_9339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_9274])).
% 9.91/3.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.91/3.73  
% 9.91/3.73  Inference rules
% 9.91/3.73  ----------------------
% 9.91/3.73  #Ref     : 0
% 9.91/3.73  #Sup     : 2247
% 9.91/3.73  #Fact    : 0
% 9.91/3.73  #Define  : 0
% 9.91/3.73  #Split   : 12
% 9.91/3.73  #Chain   : 0
% 9.91/3.73  #Close   : 0
% 9.91/3.73  
% 9.91/3.73  Ordering : KBO
% 9.91/3.73  
% 9.91/3.73  Simplification rules
% 9.91/3.73  ----------------------
% 9.91/3.73  #Subsume      : 49
% 9.91/3.73  #Demod        : 2360
% 9.91/3.73  #Tautology    : 516
% 9.91/3.73  #SimpNegUnit  : 2
% 9.91/3.73  #BackRed      : 8
% 9.91/3.73  
% 9.91/3.73  #Partial instantiations: 0
% 9.91/3.73  #Strategies tried      : 1
% 9.91/3.73  
% 9.91/3.73  Timing (in seconds)
% 9.91/3.73  ----------------------
% 9.91/3.73  Preprocessing        : 0.34
% 9.91/3.73  Parsing              : 0.18
% 9.91/3.73  CNF conversion       : 0.02
% 9.91/3.73  Main loop            : 2.64
% 9.91/3.73  Inferencing          : 0.63
% 9.91/3.73  Reduction            : 1.36
% 9.91/3.73  Demodulation         : 1.16
% 9.91/3.73  BG Simplification    : 0.10
% 9.91/3.73  Subsumption          : 0.42
% 9.91/3.73  Abstraction          : 0.14
% 9.91/3.73  MUC search           : 0.00
% 9.91/3.73  Cooper               : 0.00
% 9.91/3.73  Total                : 3.01
% 9.91/3.73  Index Insertion      : 0.00
% 9.91/3.73  Index Deletion       : 0.00
% 9.91/3.73  Index Matching       : 0.00
% 9.91/3.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
