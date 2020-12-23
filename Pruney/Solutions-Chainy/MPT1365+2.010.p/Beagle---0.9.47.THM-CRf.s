%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:55 EST 2020

% Result     : Theorem 14.32s
% Output     : CNFRefutation 14.47s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 269 expanded)
%              Number of leaves         :   30 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  210 ( 903 expanded)
%              Number of equality atoms :   16 (  62 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_subset_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v8_pre_topc(A)
                    & v2_compts_1(B,A)
                    & v2_compts_1(C,A) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & v2_compts_1(C,A) )
               => v2_compts_1(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_compts_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_88,plain,(
    ! [A_57,B_58,C_59] :
      ( k9_subset_1(A_57,B_58,C_59) = k3_xboole_0(B_58,C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,(
    ! [B_58] : k9_subset_1(u1_struct_0('#skF_1'),B_58,'#skF_3') = k3_xboole_0(B_58,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_88])).

tff(c_22,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_155,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_22])).

tff(c_156,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_155])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_28,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_24,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_392,plain,(
    ! [B_81,A_82] :
      ( v4_pre_topc(B_81,A_82)
      | ~ v2_compts_1(B_81,A_82)
      | ~ v8_pre_topc(A_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_433,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_392])).

tff(c_468,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_24,c_433])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_26,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_430,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_392])).

tff(c_465,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_26,c_430])).

tff(c_96,plain,(
    ! [B_58] : k9_subset_1(u1_struct_0('#skF_1'),B_58,'#skF_2') = k3_xboole_0(B_58,'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_88])).

tff(c_858,plain,(
    ! [A_101,B_102,C_103] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_101),B_102,C_103),A_101)
      | ~ v4_pre_topc(C_103,A_101)
      | ~ v4_pre_topc(B_102,A_101)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_867,plain,(
    ! [B_58] :
      ( v4_pre_topc(k3_xboole_0(B_58,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc('#skF_2','#skF_1')
      | ~ v4_pre_topc(B_58,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_858])).

tff(c_3145,plain,(
    ! [B_186] :
      ( v4_pre_topc(k3_xboole_0(B_186,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc(B_186,'#skF_1')
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_465,c_867])).

tff(c_3276,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3145])).

tff(c_3369,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_3276])).

tff(c_112,plain,(
    ! [A_61,B_62,C_63] :
      ( k4_subset_1(A_61,B_62,C_63) = k2_xboole_0(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_306,plain,(
    ! [B_80] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_80,'#skF_2') = k2_xboole_0(B_80,'#skF_2')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_112])).

tff(c_351,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_2') = k2_xboole_0('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_306])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k4_subset_1(A_6,B_7,C_8),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_356,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_6])).

tff(c_360,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_356])).

tff(c_624,plain,(
    ! [A_86,B_87,C_88] :
      ( v2_compts_1(k4_subset_1(u1_struct_0(A_86),B_87,C_88),A_86)
      | ~ v2_compts_1(C_88,A_86)
      | ~ v2_compts_1(B_87,A_86)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_636,plain,
    ( v2_compts_1(k2_xboole_0('#skF_2','#skF_2'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_624])).

tff(c_644,plain,(
    v2_compts_1(k2_xboole_0('#skF_2','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_32,c_26,c_26,c_636])).

tff(c_226,plain,(
    ! [A_71,B_72,C_73] :
      ( m1_subset_1(k4_subset_1(A_71,B_72,C_73),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14] :
      ( k4_subset_1(A_12,B_13,C_14) = k2_xboole_0(B_13,C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1751,plain,(
    ! [A_145,B_146,B_147,C_148] :
      ( k4_subset_1(A_145,B_146,k4_subset_1(A_145,B_147,C_148)) = k2_xboole_0(B_146,k4_subset_1(A_145,B_147,C_148))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(A_145))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_145)) ) ),
    inference(resolution,[status(thm)],[c_226,c_10])).

tff(c_2969,plain,(
    ! [B_184,C_185] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k4_subset_1(u1_struct_0('#skF_1'),B_184,C_185)) = k2_xboole_0('#skF_2',k4_subset_1(u1_struct_0('#skF_1'),B_184,C_185))
      | ~ m1_subset_1(C_185,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_1751])).

tff(c_3038,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_xboole_0('#skF_2','#skF_2')) = k2_xboole_0('#skF_2',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_2969])).

tff(c_3082,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_xboole_0('#skF_2','#skF_2')) = k2_xboole_0('#skF_2',k2_xboole_0('#skF_2','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_351,c_3038])).

tff(c_20,plain,(
    ! [A_35,B_39,C_41] :
      ( v2_compts_1(k4_subset_1(u1_struct_0(A_35),B_39,C_41),A_35)
      | ~ v2_compts_1(C_41,A_35)
      | ~ v2_compts_1(B_39,A_35)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5415,plain,
    ( v2_compts_1(k2_xboole_0('#skF_2',k2_xboole_0('#skF_2','#skF_2')),'#skF_1')
    | ~ v2_compts_1(k2_xboole_0('#skF_2','#skF_2'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3082,c_20])).

tff(c_5432,plain,(
    v2_compts_1(k2_xboole_0('#skF_2',k2_xboole_0('#skF_2','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_360,c_26,c_644,c_5415])).

tff(c_5418,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2',k2_xboole_0('#skF_2','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3082,c_6])).

tff(c_5434,plain,(
    m1_subset_1(k2_xboole_0('#skF_2',k2_xboole_0('#skF_2','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_360,c_5418])).

tff(c_98,plain,(
    ! [B_60] : k9_subset_1(u1_struct_0('#skF_1'),B_60,'#skF_2') = k3_xboole_0(B_60,'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_88])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k9_subset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [B_60] :
      ( m1_subset_1(k3_xboole_0(B_60,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_8])).

tff(c_110,plain,(
    ! [B_60] : m1_subset_1(k3_xboole_0(B_60,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_104])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : r1_tarski(k3_xboole_0(A_3,B_4),k2_xboole_0(A_3,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_734,plain,(
    ! [C_92,A_93,B_94] :
      ( v2_compts_1(C_92,A_93)
      | ~ v4_pre_topc(C_92,A_93)
      | ~ r1_tarski(C_92,B_94)
      | ~ v2_compts_1(B_94,A_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2789,plain,(
    ! [A_178,B_179,A_180,C_181] :
      ( v2_compts_1(k3_xboole_0(A_178,B_179),A_180)
      | ~ v4_pre_topc(k3_xboole_0(A_178,B_179),A_180)
      | ~ v2_compts_1(k2_xboole_0(A_178,C_181),A_180)
      | ~ m1_subset_1(k3_xboole_0(A_178,B_179),k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ m1_subset_1(k2_xboole_0(A_178,C_181),k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180) ) ),
    inference(resolution,[status(thm)],[c_4,c_734])).

tff(c_8862,plain,(
    ! [B_284,A_285,A_286,C_287] :
      ( v2_compts_1(k3_xboole_0(B_284,A_285),A_286)
      | ~ v4_pre_topc(k3_xboole_0(B_284,A_285),A_286)
      | ~ v2_compts_1(k2_xboole_0(B_284,C_287),A_286)
      | ~ m1_subset_1(k3_xboole_0(A_285,B_284),k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ m1_subset_1(k2_xboole_0(B_284,C_287),k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2789])).

tff(c_8902,plain,(
    ! [B_60,C_287] :
      ( v2_compts_1(k3_xboole_0('#skF_2',B_60),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_2',B_60),'#skF_1')
      | ~ v2_compts_1(k2_xboole_0('#skF_2',C_287),'#skF_1')
      | ~ m1_subset_1(k2_xboole_0('#skF_2',C_287),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_110,c_8862])).

tff(c_8966,plain,(
    ! [B_60,C_287] :
      ( v2_compts_1(k3_xboole_0('#skF_2',B_60),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_2',B_60),'#skF_1')
      | ~ v2_compts_1(k2_xboole_0('#skF_2',C_287),'#skF_1')
      | ~ m1_subset_1(k2_xboole_0('#skF_2',C_287),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_8902])).

tff(c_19002,plain,(
    ! [C_479] :
      ( ~ v2_compts_1(k2_xboole_0('#skF_2',C_479),'#skF_1')
      | ~ m1_subset_1(k2_xboole_0('#skF_2',C_479),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitLeft,[status(thm)],[c_8966])).

tff(c_19017,plain,(
    ~ v2_compts_1(k2_xboole_0('#skF_2',k2_xboole_0('#skF_2','#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5434,c_19002])).

tff(c_19052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5432,c_19017])).

tff(c_19054,plain,(
    ! [B_480] :
      ( v2_compts_1(k3_xboole_0('#skF_2',B_480),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_2',B_480),'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_8966])).

tff(c_19238,plain,(
    ! [A_482] :
      ( v2_compts_1(k3_xboole_0('#skF_2',A_482),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_482,'#skF_2'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_19054])).

tff(c_19241,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3369,c_19238])).

tff(c_19276,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_19241])).

tff(c_19278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_19276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:53:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.32/6.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.32/6.39  
% 14.32/6.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.32/6.39  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_subset_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 14.32/6.39  
% 14.32/6.39  %Foreground sorts:
% 14.32/6.39  
% 14.32/6.39  
% 14.32/6.39  %Background operators:
% 14.32/6.39  
% 14.32/6.39  
% 14.32/6.39  %Foreground operators:
% 14.32/6.39  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 14.32/6.39  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 14.32/6.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.32/6.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.32/6.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.32/6.39  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.32/6.39  tff('#skF_2', type, '#skF_2': $i).
% 14.32/6.39  tff('#skF_3', type, '#skF_3': $i).
% 14.32/6.39  tff('#skF_1', type, '#skF_1': $i).
% 14.32/6.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.32/6.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 14.32/6.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.32/6.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.32/6.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.32/6.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.32/6.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.32/6.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.32/6.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 14.32/6.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.32/6.39  
% 14.47/6.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.47/6.41  tff(f_129, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 14.47/6.41  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 14.47/6.41  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 14.47/6.41  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 14.47/6.41  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 14.47/6.41  tff(f_35, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 14.47/6.41  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_compts_1(B, A) & v2_compts_1(C, A)) => v2_compts_1(k4_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_compts_1)).
% 14.47/6.41  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 14.47/6.41  tff(f_29, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 14.47/6.41  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 14.47/6.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.47/6.41  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.47/6.41  tff(c_88, plain, (![A_57, B_58, C_59]: (k9_subset_1(A_57, B_58, C_59)=k3_xboole_0(B_58, C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.47/6.41  tff(c_97, plain, (![B_58]: (k9_subset_1(u1_struct_0('#skF_1'), B_58, '#skF_3')=k3_xboole_0(B_58, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_88])).
% 14.47/6.41  tff(c_22, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.47/6.41  tff(c_155, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_22])).
% 14.47/6.41  tff(c_156, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_155])).
% 14.47/6.41  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.47/6.41  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.47/6.41  tff(c_28, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.47/6.41  tff(c_24, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.47/6.41  tff(c_392, plain, (![B_81, A_82]: (v4_pre_topc(B_81, A_82) | ~v2_compts_1(B_81, A_82) | ~v8_pre_topc(A_82) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.47/6.41  tff(c_433, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_392])).
% 14.47/6.41  tff(c_468, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_24, c_433])).
% 14.47/6.41  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.47/6.41  tff(c_26, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.47/6.41  tff(c_430, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_392])).
% 14.47/6.41  tff(c_465, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_26, c_430])).
% 14.47/6.41  tff(c_96, plain, (![B_58]: (k9_subset_1(u1_struct_0('#skF_1'), B_58, '#skF_2')=k3_xboole_0(B_58, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_88])).
% 14.47/6.41  tff(c_858, plain, (![A_101, B_102, C_103]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_101), B_102, C_103), A_101) | ~v4_pre_topc(C_103, A_101) | ~v4_pre_topc(B_102, A_101) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.47/6.41  tff(c_867, plain, (![B_58]: (v4_pre_topc(k3_xboole_0(B_58, '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v4_pre_topc(B_58, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_858])).
% 14.47/6.41  tff(c_3145, plain, (![B_186]: (v4_pre_topc(k3_xboole_0(B_186, '#skF_2'), '#skF_1') | ~v4_pre_topc(B_186, '#skF_1') | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_465, c_867])).
% 14.47/6.41  tff(c_3276, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_3145])).
% 14.47/6.41  tff(c_3369, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_468, c_3276])).
% 14.47/6.41  tff(c_112, plain, (![A_61, B_62, C_63]: (k4_subset_1(A_61, B_62, C_63)=k2_xboole_0(B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.47/6.41  tff(c_306, plain, (![B_80]: (k4_subset_1(u1_struct_0('#skF_1'), B_80, '#skF_2')=k2_xboole_0(B_80, '#skF_2') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_32, c_112])).
% 14.47/6.41  tff(c_351, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_2')=k2_xboole_0('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_306])).
% 14.47/6.41  tff(c_6, plain, (![A_6, B_7, C_8]: (m1_subset_1(k4_subset_1(A_6, B_7, C_8), k1_zfmisc_1(A_6)) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.47/6.41  tff(c_356, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_351, c_6])).
% 14.47/6.41  tff(c_360, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_356])).
% 14.47/6.41  tff(c_624, plain, (![A_86, B_87, C_88]: (v2_compts_1(k4_subset_1(u1_struct_0(A_86), B_87, C_88), A_86) | ~v2_compts_1(C_88, A_86) | ~v2_compts_1(B_87, A_86) | ~m1_subset_1(C_88, k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.47/6.41  tff(c_636, plain, (v2_compts_1(k2_xboole_0('#skF_2', '#skF_2'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_351, c_624])).
% 14.47/6.41  tff(c_644, plain, (v2_compts_1(k2_xboole_0('#skF_2', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_32, c_26, c_26, c_636])).
% 14.47/6.41  tff(c_226, plain, (![A_71, B_72, C_73]: (m1_subset_1(k4_subset_1(A_71, B_72, C_73), k1_zfmisc_1(A_71)) | ~m1_subset_1(C_73, k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.47/6.41  tff(c_10, plain, (![A_12, B_13, C_14]: (k4_subset_1(A_12, B_13, C_14)=k2_xboole_0(B_13, C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.47/6.41  tff(c_1751, plain, (![A_145, B_146, B_147, C_148]: (k4_subset_1(A_145, B_146, k4_subset_1(A_145, B_147, C_148))=k2_xboole_0(B_146, k4_subset_1(A_145, B_147, C_148)) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)) | ~m1_subset_1(C_148, k1_zfmisc_1(A_145)) | ~m1_subset_1(B_147, k1_zfmisc_1(A_145)))), inference(resolution, [status(thm)], [c_226, c_10])).
% 14.47/6.41  tff(c_2969, plain, (![B_184, C_185]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k4_subset_1(u1_struct_0('#skF_1'), B_184, C_185))=k2_xboole_0('#skF_2', k4_subset_1(u1_struct_0('#skF_1'), B_184, C_185)) | ~m1_subset_1(C_185, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_32, c_1751])).
% 14.47/6.41  tff(c_3038, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_xboole_0('#skF_2', '#skF_2'))=k2_xboole_0('#skF_2', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_351, c_2969])).
% 14.47/6.41  tff(c_3082, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_xboole_0('#skF_2', '#skF_2'))=k2_xboole_0('#skF_2', k2_xboole_0('#skF_2', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_351, c_3038])).
% 14.47/6.41  tff(c_20, plain, (![A_35, B_39, C_41]: (v2_compts_1(k4_subset_1(u1_struct_0(A_35), B_39, C_41), A_35) | ~v2_compts_1(C_41, A_35) | ~v2_compts_1(B_39, A_35) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.47/6.41  tff(c_5415, plain, (v2_compts_1(k2_xboole_0('#skF_2', k2_xboole_0('#skF_2', '#skF_2')), '#skF_1') | ~v2_compts_1(k2_xboole_0('#skF_2', '#skF_2'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1(k2_xboole_0('#skF_2', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3082, c_20])).
% 14.47/6.41  tff(c_5432, plain, (v2_compts_1(k2_xboole_0('#skF_2', k2_xboole_0('#skF_2', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_360, c_26, c_644, c_5415])).
% 14.47/6.41  tff(c_5418, plain, (m1_subset_1(k2_xboole_0('#skF_2', k2_xboole_0('#skF_2', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_xboole_0('#skF_2', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3082, c_6])).
% 14.47/6.41  tff(c_5434, plain, (m1_subset_1(k2_xboole_0('#skF_2', k2_xboole_0('#skF_2', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_360, c_5418])).
% 14.47/6.41  tff(c_98, plain, (![B_60]: (k9_subset_1(u1_struct_0('#skF_1'), B_60, '#skF_2')=k3_xboole_0(B_60, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_88])).
% 14.47/6.41  tff(c_8, plain, (![A_9, B_10, C_11]: (m1_subset_1(k9_subset_1(A_9, B_10, C_11), k1_zfmisc_1(A_9)) | ~m1_subset_1(C_11, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.47/6.41  tff(c_104, plain, (![B_60]: (m1_subset_1(k3_xboole_0(B_60, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_98, c_8])).
% 14.47/6.41  tff(c_110, plain, (![B_60]: (m1_subset_1(k3_xboole_0(B_60, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_104])).
% 14.47/6.41  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(k3_xboole_0(A_3, B_4), k2_xboole_0(A_3, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.47/6.41  tff(c_734, plain, (![C_92, A_93, B_94]: (v2_compts_1(C_92, A_93) | ~v4_pre_topc(C_92, A_93) | ~r1_tarski(C_92, B_94) | ~v2_compts_1(B_94, A_93) | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.47/6.41  tff(c_2789, plain, (![A_178, B_179, A_180, C_181]: (v2_compts_1(k3_xboole_0(A_178, B_179), A_180) | ~v4_pre_topc(k3_xboole_0(A_178, B_179), A_180) | ~v2_compts_1(k2_xboole_0(A_178, C_181), A_180) | ~m1_subset_1(k3_xboole_0(A_178, B_179), k1_zfmisc_1(u1_struct_0(A_180))) | ~m1_subset_1(k2_xboole_0(A_178, C_181), k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180))), inference(resolution, [status(thm)], [c_4, c_734])).
% 14.47/6.41  tff(c_8862, plain, (![B_284, A_285, A_286, C_287]: (v2_compts_1(k3_xboole_0(B_284, A_285), A_286) | ~v4_pre_topc(k3_xboole_0(B_284, A_285), A_286) | ~v2_compts_1(k2_xboole_0(B_284, C_287), A_286) | ~m1_subset_1(k3_xboole_0(A_285, B_284), k1_zfmisc_1(u1_struct_0(A_286))) | ~m1_subset_1(k2_xboole_0(B_284, C_287), k1_zfmisc_1(u1_struct_0(A_286))) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2789])).
% 14.47/6.41  tff(c_8902, plain, (![B_60, C_287]: (v2_compts_1(k3_xboole_0('#skF_2', B_60), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', B_60), '#skF_1') | ~v2_compts_1(k2_xboole_0('#skF_2', C_287), '#skF_1') | ~m1_subset_1(k2_xboole_0('#skF_2', C_287), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_110, c_8862])).
% 14.47/6.41  tff(c_8966, plain, (![B_60, C_287]: (v2_compts_1(k3_xboole_0('#skF_2', B_60), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', B_60), '#skF_1') | ~v2_compts_1(k2_xboole_0('#skF_2', C_287), '#skF_1') | ~m1_subset_1(k2_xboole_0('#skF_2', C_287), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_8902])).
% 14.47/6.41  tff(c_19002, plain, (![C_479]: (~v2_compts_1(k2_xboole_0('#skF_2', C_479), '#skF_1') | ~m1_subset_1(k2_xboole_0('#skF_2', C_479), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_8966])).
% 14.47/6.41  tff(c_19017, plain, (~v2_compts_1(k2_xboole_0('#skF_2', k2_xboole_0('#skF_2', '#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_5434, c_19002])).
% 14.47/6.41  tff(c_19052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5432, c_19017])).
% 14.47/6.41  tff(c_19054, plain, (![B_480]: (v2_compts_1(k3_xboole_0('#skF_2', B_480), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', B_480), '#skF_1'))), inference(splitRight, [status(thm)], [c_8966])).
% 14.47/6.41  tff(c_19238, plain, (![A_482]: (v2_compts_1(k3_xboole_0('#skF_2', A_482), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_482, '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_19054])).
% 14.47/6.41  tff(c_19241, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_3369, c_19238])).
% 14.47/6.41  tff(c_19276, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_19241])).
% 14.47/6.41  tff(c_19278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_19276])).
% 14.47/6.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.47/6.41  
% 14.47/6.41  Inference rules
% 14.47/6.41  ----------------------
% 14.47/6.41  #Ref     : 0
% 14.47/6.41  #Sup     : 4455
% 14.47/6.41  #Fact    : 0
% 14.47/6.41  #Define  : 0
% 14.47/6.41  #Split   : 1
% 14.47/6.41  #Chain   : 0
% 14.47/6.41  #Close   : 0
% 14.47/6.41  
% 14.47/6.41  Ordering : KBO
% 14.47/6.41  
% 14.47/6.41  Simplification rules
% 14.47/6.41  ----------------------
% 14.47/6.41  #Subsume      : 31
% 14.47/6.41  #Demod        : 5179
% 14.47/6.41  #Tautology    : 826
% 14.47/6.41  #SimpNegUnit  : 3
% 14.47/6.41  #BackRed      : 1
% 14.47/6.41  
% 14.47/6.41  #Partial instantiations: 0
% 14.47/6.41  #Strategies tried      : 1
% 14.47/6.41  
% 14.47/6.41  Timing (in seconds)
% 14.47/6.41  ----------------------
% 14.47/6.41  Preprocessing        : 0.34
% 14.47/6.41  Parsing              : 0.18
% 14.47/6.41  CNF conversion       : 0.02
% 14.47/6.41  Main loop            : 5.29
% 14.47/6.41  Inferencing          : 1.00
% 14.47/6.41  Reduction            : 2.90
% 14.47/6.41  Demodulation         : 2.56
% 14.47/6.41  BG Simplification    : 0.14
% 14.47/6.41  Subsumption          : 0.96
% 14.47/6.41  Abstraction          : 0.24
% 14.47/6.41  MUC search           : 0.00
% 14.47/6.41  Cooper               : 0.00
% 14.47/6.41  Total                : 5.67
% 14.47/6.41  Index Insertion      : 0.00
% 14.47/6.41  Index Deletion       : 0.00
% 14.47/6.41  Index Matching       : 0.00
% 14.47/6.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
