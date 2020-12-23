%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:58 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 109 expanded)
%              Number of leaves         :   32 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  121 ( 333 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_115,negated_conjecture,(
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

tff(f_47,axiom,(
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

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

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

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_72,plain,(
    ! [A_71,B_72,C_73] :
      ( k9_subset_1(A_71,B_72,C_73) = k3_xboole_0(B_72,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,(
    ! [B_72] : k9_subset_1(u1_struct_0('#skF_1'),B_72,'#skF_3') = k3_xboole_0(B_72,'#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_72])).

tff(c_28,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_109,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_28])).

tff(c_32,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_218,plain,(
    ! [B_113,A_114] :
      ( v4_pre_topc(B_113,A_114)
      | ~ v2_compts_1(B_113,A_114)
      | ~ v8_pre_topc(A_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_243,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_218])).

tff(c_268,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_32,c_243])).

tff(c_30,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_246,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_218])).

tff(c_271,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_30,c_246])).

tff(c_512,plain,(
    ! [A_190,B_191,C_192] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_190),B_191,C_192),A_190)
      | ~ v4_pre_topc(C_192,A_190)
      | ~ v4_pre_topc(B_191,A_190)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_543,plain,(
    ! [B_72] :
      ( v4_pre_topc(k3_xboole_0(B_72,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_72,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_512])).

tff(c_567,plain,(
    ! [B_193] :
      ( v4_pre_topc(k3_xboole_0(B_193,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_193,'#skF_1')
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_271,c_543])).

tff(c_604,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_567])).

tff(c_621,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_604])).

tff(c_110,plain,(
    ! [B_80] : k9_subset_1(u1_struct_0('#skF_1'),B_80,'#skF_3') = k3_xboole_0(B_80,'#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_72])).

tff(c_16,plain,(
    ! [A_30,B_31,C_32] :
      ( m1_subset_1(k9_subset_1(A_30,B_31,C_32),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_116,plain,(
    ! [B_80] :
      ( m1_subset_1(k3_xboole_0(B_80,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_16])).

tff(c_122,plain,(
    ! [B_80] : m1_subset_1(k3_xboole_0(B_80,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_116])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_375,plain,(
    ! [C_154,A_155,B_156] :
      ( v2_compts_1(C_154,A_155)
      | ~ v4_pre_topc(C_154,A_155)
      | ~ r1_tarski(C_154,B_156)
      | ~ v2_compts_1(B_156,A_155)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_750,plain,(
    ! [A_220,B_221,A_222] :
      ( v2_compts_1(k3_xboole_0(A_220,B_221),A_222)
      | ~ v4_pre_topc(k3_xboole_0(A_220,B_221),A_222)
      | ~ v2_compts_1(A_220,A_222)
      | ~ m1_subset_1(k3_xboole_0(A_220,B_221),k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ m1_subset_1(A_220,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222) ) ),
    inference(resolution,[status(thm)],[c_2,c_375])).

tff(c_777,plain,(
    ! [B_80] :
      ( v2_compts_1(k3_xboole_0(B_80,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_80,'#skF_3'),'#skF_1')
      | ~ v2_compts_1(B_80,'#skF_1')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_122,c_750])).

tff(c_811,plain,(
    ! [B_223] :
      ( v2_compts_1(k3_xboole_0(B_223,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_223,'#skF_3'),'#skF_1')
      | ~ v2_compts_1(B_223,'#skF_1')
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_777])).

tff(c_848,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_811])).

tff(c_865,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_621,c_848])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.52  
% 3.09/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.52  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.09/1.52  
% 3.09/1.52  %Foreground sorts:
% 3.09/1.52  
% 3.09/1.52  
% 3.09/1.52  %Background operators:
% 3.09/1.52  
% 3.09/1.52  
% 3.09/1.52  %Foreground operators:
% 3.09/1.52  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.09/1.52  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.09/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.09/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.09/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.52  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.09/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.09/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.09/1.52  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.09/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.09/1.52  
% 3.09/1.53  tff(f_115, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 3.09/1.53  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.09/1.53  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 3.09/1.53  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 3.09/1.53  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.09/1.53  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.09/1.53  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 3.09/1.53  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.09/1.53  tff(c_72, plain, (![A_71, B_72, C_73]: (k9_subset_1(A_71, B_72, C_73)=k3_xboole_0(B_72, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.53  tff(c_81, plain, (![B_72]: (k9_subset_1(u1_struct_0('#skF_1'), B_72, '#skF_3')=k3_xboole_0(B_72, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_72])).
% 3.09/1.53  tff(c_28, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.09/1.53  tff(c_109, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_28])).
% 3.09/1.53  tff(c_32, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.09/1.53  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.09/1.53  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.09/1.53  tff(c_34, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.09/1.53  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.09/1.53  tff(c_218, plain, (![B_113, A_114]: (v4_pre_topc(B_113, A_114) | ~v2_compts_1(B_113, A_114) | ~v8_pre_topc(A_114) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.53  tff(c_243, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_218])).
% 3.09/1.53  tff(c_268, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_32, c_243])).
% 3.09/1.53  tff(c_30, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.09/1.53  tff(c_246, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_218])).
% 3.09/1.53  tff(c_271, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_30, c_246])).
% 3.09/1.53  tff(c_512, plain, (![A_190, B_191, C_192]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_190), B_191, C_192), A_190) | ~v4_pre_topc(C_192, A_190) | ~v4_pre_topc(B_191, A_190) | ~m1_subset_1(C_192, k1_zfmisc_1(u1_struct_0(A_190))) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.09/1.53  tff(c_543, plain, (![B_72]: (v4_pre_topc(k3_xboole_0(B_72, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_72, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_512])).
% 3.09/1.53  tff(c_567, plain, (![B_193]: (v4_pre_topc(k3_xboole_0(B_193, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_193, '#skF_1') | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_271, c_543])).
% 3.09/1.53  tff(c_604, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_567])).
% 3.09/1.53  tff(c_621, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_604])).
% 3.09/1.53  tff(c_110, plain, (![B_80]: (k9_subset_1(u1_struct_0('#skF_1'), B_80, '#skF_3')=k3_xboole_0(B_80, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_72])).
% 3.09/1.53  tff(c_16, plain, (![A_30, B_31, C_32]: (m1_subset_1(k9_subset_1(A_30, B_31, C_32), k1_zfmisc_1(A_30)) | ~m1_subset_1(C_32, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.09/1.53  tff(c_116, plain, (![B_80]: (m1_subset_1(k3_xboole_0(B_80, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_110, c_16])).
% 3.09/1.53  tff(c_122, plain, (![B_80]: (m1_subset_1(k3_xboole_0(B_80, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_116])).
% 3.09/1.53  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.09/1.53  tff(c_375, plain, (![C_154, A_155, B_156]: (v2_compts_1(C_154, A_155) | ~v4_pre_topc(C_154, A_155) | ~r1_tarski(C_154, B_156) | ~v2_compts_1(B_156, A_155) | ~m1_subset_1(C_154, k1_zfmisc_1(u1_struct_0(A_155))) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.09/1.53  tff(c_750, plain, (![A_220, B_221, A_222]: (v2_compts_1(k3_xboole_0(A_220, B_221), A_222) | ~v4_pre_topc(k3_xboole_0(A_220, B_221), A_222) | ~v2_compts_1(A_220, A_222) | ~m1_subset_1(k3_xboole_0(A_220, B_221), k1_zfmisc_1(u1_struct_0(A_222))) | ~m1_subset_1(A_220, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222))), inference(resolution, [status(thm)], [c_2, c_375])).
% 3.09/1.53  tff(c_777, plain, (![B_80]: (v2_compts_1(k3_xboole_0(B_80, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_80, '#skF_3'), '#skF_1') | ~v2_compts_1(B_80, '#skF_1') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_122, c_750])).
% 3.09/1.53  tff(c_811, plain, (![B_223]: (v2_compts_1(k3_xboole_0(B_223, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_223, '#skF_3'), '#skF_1') | ~v2_compts_1(B_223, '#skF_1') | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_777])).
% 3.09/1.53  tff(c_848, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_811])).
% 3.09/1.53  tff(c_865, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_621, c_848])).
% 3.09/1.53  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_865])).
% 3.09/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.53  
% 3.09/1.53  Inference rules
% 3.09/1.53  ----------------------
% 3.09/1.53  #Ref     : 0
% 3.09/1.53  #Sup     : 172
% 3.09/1.53  #Fact    : 0
% 3.09/1.53  #Define  : 0
% 3.09/1.53  #Split   : 0
% 3.09/1.53  #Chain   : 0
% 3.09/1.53  #Close   : 0
% 3.09/1.53  
% 3.09/1.53  Ordering : KBO
% 3.09/1.53  
% 3.09/1.53  Simplification rules
% 3.09/1.53  ----------------------
% 3.09/1.53  #Subsume      : 8
% 3.09/1.53  #Demod        : 216
% 3.09/1.53  #Tautology    : 47
% 3.09/1.53  #SimpNegUnit  : 1
% 3.09/1.53  #BackRed      : 1
% 3.09/1.53  
% 3.09/1.53  #Partial instantiations: 0
% 3.09/1.53  #Strategies tried      : 1
% 3.09/1.53  
% 3.09/1.53  Timing (in seconds)
% 3.09/1.53  ----------------------
% 3.45/1.54  Preprocessing        : 0.34
% 3.45/1.54  Parsing              : 0.18
% 3.45/1.54  CNF conversion       : 0.02
% 3.45/1.54  Main loop            : 0.44
% 3.45/1.54  Inferencing          : 0.17
% 3.45/1.54  Reduction            : 0.15
% 3.45/1.54  Demodulation         : 0.12
% 3.45/1.54  BG Simplification    : 0.03
% 3.45/1.54  Subsumption          : 0.06
% 3.45/1.54  Abstraction          : 0.03
% 3.45/1.54  MUC search           : 0.00
% 3.45/1.54  Cooper               : 0.00
% 3.45/1.54  Total                : 0.81
% 3.45/1.54  Index Insertion      : 0.00
% 3.45/1.54  Index Deletion       : 0.00
% 3.45/1.54  Index Matching       : 0.00
% 3.45/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
