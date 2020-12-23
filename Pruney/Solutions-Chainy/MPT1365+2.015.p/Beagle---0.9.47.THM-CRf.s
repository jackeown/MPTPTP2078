%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:56 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 160 expanded)
%              Number of leaves         :   31 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  134 ( 466 expanded)
%              Number of equality atoms :   14 (  44 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_113,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_63,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_94,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_91,plain,(
    ! [A_52,B_53,C_54] :
      ( k9_subset_1(A_52,B_53,C_54) = k3_xboole_0(B_53,C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [B_53] : k9_subset_1(u1_struct_0('#skF_1'),B_53,'#skF_2') = k3_xboole_0(B_53,'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_91])).

tff(c_187,plain,(
    ! [A_65,C_66,B_67] :
      ( k9_subset_1(A_65,C_66,B_67) = k9_subset_1(A_65,B_67,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_199,plain,(
    ! [B_67] : k9_subset_1(u1_struct_0('#skF_1'),B_67,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_67) ),
    inference(resolution,[status(thm)],[c_32,c_187])).

tff(c_211,plain,(
    ! [B_68] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_68) = k3_xboole_0(B_68,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_199])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_97,plain,(
    ! [B_53] : k9_subset_1(u1_struct_0('#skF_1'),B_53,'#skF_3') = k3_xboole_0(B_53,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_91])).

tff(c_218,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_97])).

tff(c_22,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_116,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_22])).

tff(c_238,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_116])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_294,plain,(
    ! [B_70,A_71] :
      ( v4_pre_topc(B_70,A_71)
      | ~ v2_compts_1(B_70,A_71)
      | ~ v8_pre_topc(A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_316,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_294])).

tff(c_335,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_24,c_316])).

tff(c_26,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_313,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_294])).

tff(c_332,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_26,c_313])).

tff(c_550,plain,(
    ! [A_91,B_92,C_93] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_91),B_92,C_93),A_91)
      | ~ v4_pre_topc(C_93,A_91)
      | ~ v4_pre_topc(B_92,A_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_562,plain,(
    ! [B_53] :
      ( v4_pre_topc(k3_xboole_0(B_53,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc('#skF_2','#skF_1')
      | ~ v4_pre_topc(B_53,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_550])).

tff(c_574,plain,(
    ! [B_94] :
      ( v4_pre_topc(k3_xboole_0(B_94,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc(B_94,'#skF_1')
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_332,c_562])).

tff(c_614,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_574])).

tff(c_631,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_614])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_48,B_49,C_50] :
      ( k7_subset_1(A_48,B_49,C_50) = k4_xboole_0(B_49,C_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [C_50] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_50) = k4_xboole_0('#skF_2',C_50) ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_126,plain,(
    ! [A_58,B_59,C_60] :
      ( m1_subset_1(k7_subset_1(A_58,B_59,C_60),k1_zfmisc_1(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [C_50] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_50),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_126])).

tff(c_158,plain,(
    ! [C_62] : m1_subset_1(k4_xboole_0('#skF_2',C_62),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_136])).

tff(c_170,plain,(
    ! [B_4] : m1_subset_1(k3_xboole_0('#skF_2',B_4),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_158])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_503,plain,(
    ! [C_84,A_85,B_86] :
      ( v2_compts_1(C_84,A_85)
      | ~ v4_pre_topc(C_84,A_85)
      | ~ r1_tarski(C_84,B_86)
      | ~ v2_compts_1(B_86,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1705,plain,(
    ! [A_146,B_147,A_148] :
      ( v2_compts_1(k3_xboole_0(A_146,B_147),A_148)
      | ~ v4_pre_topc(k3_xboole_0(A_146,B_147),A_148)
      | ~ v2_compts_1(A_146,A_148)
      | ~ m1_subset_1(k3_xboole_0(A_146,B_147),k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ m1_subset_1(A_146,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_2,c_503])).

tff(c_1741,plain,(
    ! [B_4] :
      ( v2_compts_1(k3_xboole_0('#skF_2',B_4),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_2',B_4),'#skF_1')
      | ~ v2_compts_1('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_170,c_1705])).

tff(c_1824,plain,(
    ! [B_151] :
      ( v2_compts_1(k3_xboole_0('#skF_2',B_151),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_2',B_151),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_26,c_1741])).

tff(c_1833,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_1824])).

tff(c_1837,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_218,c_1833])).

tff(c_1839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_1837])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:46:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.65  
% 3.65/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.65  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.65/1.65  
% 3.65/1.65  %Foreground sorts:
% 3.65/1.65  
% 3.65/1.65  
% 3.65/1.65  %Background operators:
% 3.65/1.65  
% 3.65/1.65  
% 3.65/1.65  %Foreground operators:
% 3.65/1.65  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.65/1.65  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.65/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.65/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.65/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.65/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.65/1.65  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.65/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.65/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.65/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.65/1.65  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.65/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.65/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.65/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.65/1.65  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.65/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.65/1.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.65/1.65  
% 3.99/1.67  tff(f_113, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 3.99/1.67  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.99/1.67  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.99/1.67  tff(f_76, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 3.99/1.67  tff(f_63, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_1)).
% 3.99/1.67  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.99/1.67  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.99/1.67  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 3.99/1.67  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.99/1.67  tff(f_94, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 3.99/1.67  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.67  tff(c_91, plain, (![A_52, B_53, C_54]: (k9_subset_1(A_52, B_53, C_54)=k3_xboole_0(B_53, C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.99/1.67  tff(c_96, plain, (![B_53]: (k9_subset_1(u1_struct_0('#skF_1'), B_53, '#skF_2')=k3_xboole_0(B_53, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_91])).
% 3.99/1.67  tff(c_187, plain, (![A_65, C_66, B_67]: (k9_subset_1(A_65, C_66, B_67)=k9_subset_1(A_65, B_67, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.99/1.67  tff(c_199, plain, (![B_67]: (k9_subset_1(u1_struct_0('#skF_1'), B_67, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_67))), inference(resolution, [status(thm)], [c_32, c_187])).
% 3.99/1.67  tff(c_211, plain, (![B_68]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_68)=k3_xboole_0(B_68, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_199])).
% 3.99/1.67  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.67  tff(c_97, plain, (![B_53]: (k9_subset_1(u1_struct_0('#skF_1'), B_53, '#skF_3')=k3_xboole_0(B_53, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_91])).
% 3.99/1.67  tff(c_218, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_211, c_97])).
% 3.99/1.67  tff(c_22, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.67  tff(c_116, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_22])).
% 3.99/1.67  tff(c_238, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_116])).
% 3.99/1.67  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.67  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.67  tff(c_28, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.67  tff(c_24, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.67  tff(c_294, plain, (![B_70, A_71]: (v4_pre_topc(B_70, A_71) | ~v2_compts_1(B_70, A_71) | ~v8_pre_topc(A_71) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.99/1.67  tff(c_316, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_294])).
% 3.99/1.67  tff(c_335, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_24, c_316])).
% 3.99/1.67  tff(c_26, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.67  tff(c_313, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_294])).
% 3.99/1.67  tff(c_332, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_26, c_313])).
% 3.99/1.67  tff(c_550, plain, (![A_91, B_92, C_93]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_91), B_92, C_93), A_91) | ~v4_pre_topc(C_93, A_91) | ~v4_pre_topc(B_92, A_91) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_91))) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.99/1.67  tff(c_562, plain, (![B_53]: (v4_pre_topc(k3_xboole_0(B_53, '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v4_pre_topc(B_53, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_550])).
% 3.99/1.67  tff(c_574, plain, (![B_94]: (v4_pre_topc(k3_xboole_0(B_94, '#skF_2'), '#skF_1') | ~v4_pre_topc(B_94, '#skF_1') | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_332, c_562])).
% 3.99/1.67  tff(c_614, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_574])).
% 3.99/1.67  tff(c_631, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_614])).
% 3.99/1.67  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.99/1.67  tff(c_75, plain, (![A_48, B_49, C_50]: (k7_subset_1(A_48, B_49, C_50)=k4_xboole_0(B_49, C_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.99/1.67  tff(c_80, plain, (![C_50]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_50)=k4_xboole_0('#skF_2', C_50))), inference(resolution, [status(thm)], [c_32, c_75])).
% 3.99/1.67  tff(c_126, plain, (![A_58, B_59, C_60]: (m1_subset_1(k7_subset_1(A_58, B_59, C_60), k1_zfmisc_1(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.99/1.67  tff(c_136, plain, (![C_50]: (m1_subset_1(k4_xboole_0('#skF_2', C_50), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_80, c_126])).
% 3.99/1.67  tff(c_158, plain, (![C_62]: (m1_subset_1(k4_xboole_0('#skF_2', C_62), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_136])).
% 3.99/1.67  tff(c_170, plain, (![B_4]: (m1_subset_1(k3_xboole_0('#skF_2', B_4), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_158])).
% 3.99/1.67  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.99/1.67  tff(c_503, plain, (![C_84, A_85, B_86]: (v2_compts_1(C_84, A_85) | ~v4_pre_topc(C_84, A_85) | ~r1_tarski(C_84, B_86) | ~v2_compts_1(B_86, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.99/1.67  tff(c_1705, plain, (![A_146, B_147, A_148]: (v2_compts_1(k3_xboole_0(A_146, B_147), A_148) | ~v4_pre_topc(k3_xboole_0(A_146, B_147), A_148) | ~v2_compts_1(A_146, A_148) | ~m1_subset_1(k3_xboole_0(A_146, B_147), k1_zfmisc_1(u1_struct_0(A_148))) | ~m1_subset_1(A_146, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148))), inference(resolution, [status(thm)], [c_2, c_503])).
% 3.99/1.67  tff(c_1741, plain, (![B_4]: (v2_compts_1(k3_xboole_0('#skF_2', B_4), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', B_4), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_170, c_1705])).
% 3.99/1.67  tff(c_1824, plain, (![B_151]: (v2_compts_1(k3_xboole_0('#skF_2', B_151), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', B_151), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_26, c_1741])).
% 3.99/1.67  tff(c_1833, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_218, c_1824])).
% 3.99/1.67  tff(c_1837, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_631, c_218, c_1833])).
% 3.99/1.67  tff(c_1839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_1837])).
% 3.99/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.67  
% 3.99/1.67  Inference rules
% 3.99/1.67  ----------------------
% 3.99/1.67  #Ref     : 0
% 3.99/1.67  #Sup     : 425
% 3.99/1.67  #Fact    : 0
% 3.99/1.67  #Define  : 0
% 3.99/1.67  #Split   : 0
% 3.99/1.67  #Chain   : 0
% 3.99/1.67  #Close   : 0
% 3.99/1.67  
% 3.99/1.67  Ordering : KBO
% 3.99/1.67  
% 3.99/1.67  Simplification rules
% 3.99/1.67  ----------------------
% 3.99/1.67  #Subsume      : 7
% 3.99/1.67  #Demod        : 339
% 3.99/1.67  #Tautology    : 118
% 3.99/1.67  #SimpNegUnit  : 1
% 3.99/1.67  #BackRed      : 4
% 3.99/1.67  
% 3.99/1.67  #Partial instantiations: 0
% 3.99/1.67  #Strategies tried      : 1
% 3.99/1.67  
% 3.99/1.67  Timing (in seconds)
% 3.99/1.67  ----------------------
% 3.99/1.67  Preprocessing        : 0.30
% 3.99/1.67  Parsing              : 0.16
% 3.99/1.67  CNF conversion       : 0.02
% 3.99/1.67  Main loop            : 0.57
% 3.99/1.67  Inferencing          : 0.18
% 3.99/1.67  Reduction            : 0.23
% 3.99/1.67  Demodulation         : 0.18
% 3.99/1.67  BG Simplification    : 0.03
% 3.99/1.67  Subsumption          : 0.08
% 3.99/1.67  Abstraction          : 0.04
% 3.99/1.67  MUC search           : 0.00
% 3.99/1.67  Cooper               : 0.00
% 3.99/1.67  Total                : 0.90
% 3.99/1.67  Index Insertion      : 0.00
% 3.99/1.67  Index Deletion       : 0.00
% 3.99/1.67  Index Matching       : 0.00
% 3.99/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
