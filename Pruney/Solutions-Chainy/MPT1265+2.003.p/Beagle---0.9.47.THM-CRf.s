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
% DateTime   : Thu Dec  3 10:21:42 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 100 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 244 expanded)
%              Number of equality atoms :   33 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & v1_tops_1(C,A)
                    & v3_pre_topc(C,A) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( v3_pre_topc(C,A)
                 => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_26,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_198,plain,(
    ! [A_47,B_48,C_49] :
      ( k9_subset_1(A_47,B_48,C_49) = k3_xboole_0(B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_203,plain,(
    ! [B_48] : k9_subset_1(u1_struct_0('#skF_1'),B_48,'#skF_2') = k3_xboole_0(B_48,'#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_198])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_631,plain,(
    ! [A_77,B_78] :
      ( k2_pre_topc(A_77,B_78) = k2_struct_0(A_77)
      | ~ v1_tops_1(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_674,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_631])).

tff(c_714,plain,(
    k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24,c_674])).

tff(c_829,plain,(
    ! [A_85,C_86,B_87] :
      ( k2_pre_topc(A_85,k9_subset_1(u1_struct_0(A_85),C_86,B_87)) = k2_pre_topc(A_85,C_86)
      | ~ v3_pre_topc(C_86,A_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ v1_tops_1(B_87,A_85)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_862,plain,(
    ! [B_87] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_87)) = k2_pre_topc('#skF_1','#skF_3')
      | ~ v3_pre_topc('#skF_3','#skF_1')
      | ~ v1_tops_1(B_87,'#skF_1')
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_829])).

tff(c_953,plain,(
    ! [B_90] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_90)) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_90,'#skF_1')
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_22,c_714,c_862])).

tff(c_1002,plain,
    ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_953])).

tff(c_1024,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_203,c_1002])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_155,plain,(
    ! [A_40,B_41,C_42] :
      ( k7_subset_1(A_40,B_41,C_42) = k4_xboole_0(B_41,C_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_161,plain,(
    ! [C_42] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',C_42) = k4_xboole_0('#skF_3',C_42) ),
    inference(resolution,[status(thm)],[c_28,c_155])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k7_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_378,plain,(
    ! [B_63,A_64] :
      ( v1_tops_1(B_63,A_64)
      | k2_pre_topc(A_64,B_63) != k2_struct_0(A_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1827,plain,(
    ! [A_128,B_129,C_130] :
      ( v1_tops_1(k7_subset_1(u1_struct_0(A_128),B_129,C_130),A_128)
      | k2_pre_topc(A_128,k7_subset_1(u1_struct_0(A_128),B_129,C_130)) != k2_struct_0(A_128)
      | ~ l1_pre_topc(A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128))) ) ),
    inference(resolution,[status(thm)],[c_6,c_378])).

tff(c_1839,plain,(
    ! [C_42] :
      ( v1_tops_1(k4_xboole_0('#skF_3',C_42),'#skF_1')
      | k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',C_42)) != k2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_1827])).

tff(c_1891,plain,(
    ! [C_133] :
      ( v1_tops_1(k4_xboole_0('#skF_3',C_133),'#skF_1')
      | k2_pre_topc('#skF_1',k4_xboole_0('#skF_3',C_133)) != k2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_161,c_1839])).

tff(c_1906,plain,(
    ! [B_2] :
      ( v1_tops_1(k3_xboole_0('#skF_3',B_2),'#skF_1')
      | k2_pre_topc('#skF_1',k4_xboole_0('#skF_3',k4_xboole_0('#skF_3',B_2))) != k2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1891])).

tff(c_2124,plain,(
    ! [B_141] :
      ( v1_tops_1(k3_xboole_0('#skF_3',B_141),'#skF_1')
      | k2_pre_topc('#skF_1',k3_xboole_0('#skF_3',B_141)) != k2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1906])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [B_34,A_35] : k1_setfam_1(k2_tarski(B_34,A_35)) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_68])).

tff(c_12,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_89,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12])).

tff(c_204,plain,(
    ! [B_48] : k9_subset_1(u1_struct_0('#skF_1'),B_48,'#skF_3') = k3_xboole_0(B_48,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_198])).

tff(c_20,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_214,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_20])).

tff(c_215,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_214])).

tff(c_2130,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2124,c_215])).

tff(c_2143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_2130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.69  
% 3.69/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.69  %$ v3_pre_topc > v1_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.69/1.69  
% 3.69/1.69  %Foreground sorts:
% 3.69/1.69  
% 3.69/1.69  
% 3.69/1.69  %Background operators:
% 3.69/1.69  
% 3.69/1.69  
% 3.69/1.69  %Foreground operators:
% 3.69/1.69  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.69/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.69/1.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.69/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.69/1.69  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.69/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.69/1.69  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.69/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.69/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.69/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.69/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.69/1.69  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.69/1.69  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.69/1.69  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.69/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.69  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.69/1.69  
% 4.03/1.70  tff(f_87, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v1_tops_1(B, A) & v1_tops_1(C, A)) & v3_pre_topc(C, A)) => v1_tops_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_tops_1)).
% 4.03/1.70  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.03/1.70  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 4.03/1.70  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 4.03/1.70  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.03/1.70  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.03/1.70  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.03/1.70  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.03/1.70  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.03/1.70  tff(c_26, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.03/1.70  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.03/1.70  tff(c_198, plain, (![A_47, B_48, C_49]: (k9_subset_1(A_47, B_48, C_49)=k3_xboole_0(B_48, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.03/1.70  tff(c_203, plain, (![B_48]: (k9_subset_1(u1_struct_0('#skF_1'), B_48, '#skF_2')=k3_xboole_0(B_48, '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_198])).
% 4.03/1.70  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.03/1.70  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.03/1.70  tff(c_22, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.03/1.70  tff(c_24, plain, (v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.03/1.70  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.03/1.70  tff(c_631, plain, (![A_77, B_78]: (k2_pre_topc(A_77, B_78)=k2_struct_0(A_77) | ~v1_tops_1(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.03/1.70  tff(c_674, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_631])).
% 4.03/1.70  tff(c_714, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24, c_674])).
% 4.03/1.70  tff(c_829, plain, (![A_85, C_86, B_87]: (k2_pre_topc(A_85, k9_subset_1(u1_struct_0(A_85), C_86, B_87))=k2_pre_topc(A_85, C_86) | ~v3_pre_topc(C_86, A_85) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~v1_tops_1(B_87, A_85) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.70  tff(c_862, plain, (![B_87]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_87))=k2_pre_topc('#skF_1', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_1') | ~v1_tops_1(B_87, '#skF_1') | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_829])).
% 4.03/1.70  tff(c_953, plain, (![B_90]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_90))=k2_struct_0('#skF_1') | ~v1_tops_1(B_90, '#skF_1') | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_22, c_714, c_862])).
% 4.03/1.70  tff(c_1002, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_953])).
% 4.03/1.70  tff(c_1024, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_203, c_1002])).
% 4.03/1.70  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.03/1.70  tff(c_155, plain, (![A_40, B_41, C_42]: (k7_subset_1(A_40, B_41, C_42)=k4_xboole_0(B_41, C_42) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.03/1.70  tff(c_161, plain, (![C_42]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', C_42)=k4_xboole_0('#skF_3', C_42))), inference(resolution, [status(thm)], [c_28, c_155])).
% 4.03/1.70  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k7_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.03/1.70  tff(c_378, plain, (![B_63, A_64]: (v1_tops_1(B_63, A_64) | k2_pre_topc(A_64, B_63)!=k2_struct_0(A_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.03/1.70  tff(c_1827, plain, (![A_128, B_129, C_130]: (v1_tops_1(k7_subset_1(u1_struct_0(A_128), B_129, C_130), A_128) | k2_pre_topc(A_128, k7_subset_1(u1_struct_0(A_128), B_129, C_130))!=k2_struct_0(A_128) | ~l1_pre_topc(A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))))), inference(resolution, [status(thm)], [c_6, c_378])).
% 4.03/1.70  tff(c_1839, plain, (![C_42]: (v1_tops_1(k4_xboole_0('#skF_3', C_42), '#skF_1') | k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', C_42))!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_161, c_1827])).
% 4.03/1.70  tff(c_1891, plain, (![C_133]: (v1_tops_1(k4_xboole_0('#skF_3', C_133), '#skF_1') | k2_pre_topc('#skF_1', k4_xboole_0('#skF_3', C_133))!=k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_161, c_1839])).
% 4.03/1.70  tff(c_1906, plain, (![B_2]: (v1_tops_1(k3_xboole_0('#skF_3', B_2), '#skF_1') | k2_pre_topc('#skF_1', k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', B_2)))!=k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1891])).
% 4.03/1.70  tff(c_2124, plain, (![B_141]: (v1_tops_1(k3_xboole_0('#skF_3', B_141), '#skF_1') | k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', B_141))!=k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1906])).
% 4.03/1.70  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.03/1.70  tff(c_68, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.03/1.70  tff(c_83, plain, (![B_34, A_35]: (k1_setfam_1(k2_tarski(B_34, A_35))=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_4, c_68])).
% 4.03/1.70  tff(c_12, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.03/1.70  tff(c_89, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_83, c_12])).
% 4.03/1.70  tff(c_204, plain, (![B_48]: (k9_subset_1(u1_struct_0('#skF_1'), B_48, '#skF_3')=k3_xboole_0(B_48, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_198])).
% 4.03/1.70  tff(c_20, plain, (~v1_tops_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.03/1.70  tff(c_214, plain, (~v1_tops_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_20])).
% 4.03/1.70  tff(c_215, plain, (~v1_tops_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_214])).
% 4.03/1.70  tff(c_2130, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2124, c_215])).
% 4.03/1.70  tff(c_2143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1024, c_2130])).
% 4.03/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.70  
% 4.03/1.70  Inference rules
% 4.03/1.70  ----------------------
% 4.03/1.70  #Ref     : 0
% 4.03/1.70  #Sup     : 473
% 4.03/1.70  #Fact    : 0
% 4.03/1.70  #Define  : 0
% 4.03/1.70  #Split   : 1
% 4.03/1.70  #Chain   : 0
% 4.03/1.70  #Close   : 0
% 4.03/1.70  
% 4.03/1.70  Ordering : KBO
% 4.03/1.70  
% 4.03/1.70  Simplification rules
% 4.03/1.70  ----------------------
% 4.03/1.70  #Subsume      : 3
% 4.03/1.70  #Demod        : 334
% 4.03/1.70  #Tautology    : 155
% 4.03/1.70  #SimpNegUnit  : 0
% 4.03/1.70  #BackRed      : 1
% 4.03/1.70  
% 4.03/1.70  #Partial instantiations: 0
% 4.03/1.70  #Strategies tried      : 1
% 4.03/1.70  
% 4.03/1.70  Timing (in seconds)
% 4.03/1.70  ----------------------
% 4.03/1.71  Preprocessing        : 0.31
% 4.03/1.71  Parsing              : 0.17
% 4.03/1.71  CNF conversion       : 0.02
% 4.03/1.71  Main loop            : 0.61
% 4.03/1.71  Inferencing          : 0.18
% 4.03/1.71  Reduction            : 0.27
% 4.03/1.71  Demodulation         : 0.22
% 4.03/1.71  BG Simplification    : 0.03
% 4.03/1.71  Subsumption          : 0.08
% 4.03/1.71  Abstraction          : 0.04
% 4.03/1.71  MUC search           : 0.00
% 4.03/1.71  Cooper               : 0.00
% 4.03/1.71  Total                : 0.95
% 4.03/1.71  Index Insertion      : 0.00
% 4.03/1.71  Index Deletion       : 0.00
% 4.03/1.71  Index Matching       : 0.00
% 4.03/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
