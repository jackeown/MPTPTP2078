%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:57 EST 2020

% Result     : Theorem 5.71s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 138 expanded)
%              Number of leaves         :   30 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  141 ( 387 expanded)
%              Number of equality atoms :    6 (  26 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k2_enumset1 > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_61,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
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

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_87,plain,(
    ! [A_47,B_48,C_49] :
      ( k9_subset_1(A_47,B_48,C_49) = k3_xboole_0(B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    ! [B_48] : k9_subset_1(u1_struct_0('#skF_1'),B_48,'#skF_3') = k3_xboole_0(B_48,'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_87])).

tff(c_24,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_109,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_24])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_172,plain,(
    ! [B_62,A_63] :
      ( v4_pre_topc(B_62,A_63)
      | ~ v2_compts_1(B_62,A_63)
      | ~ v8_pre_topc(A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_190,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_172])).

tff(c_203,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_28,c_190])).

tff(c_26,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_187,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_172])).

tff(c_200,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_26,c_187])).

tff(c_382,plain,(
    ! [A_94,B_95,C_96] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_94),B_95,C_96),A_94)
      | ~ v4_pre_topc(C_96,A_94)
      | ~ v4_pre_topc(B_95,A_94)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_395,plain,(
    ! [B_48] :
      ( v4_pre_topc(k3_xboole_0(B_48,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_48,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_382])).

tff(c_470,plain,(
    ! [B_104] :
      ( v4_pre_topc(k3_xboole_0(B_104,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_104,'#skF_1')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_200,c_395])).

tff(c_504,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_470])).

tff(c_522,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_504])).

tff(c_141,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1(k9_subset_1(A_57,B_58,C_59),k1_zfmisc_1(A_57))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_152,plain,(
    ! [B_48] :
      ( m1_subset_1(k3_xboole_0(B_48,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_141])).

tff(c_161,plain,(
    ! [B_48] : m1_subset_1(k3_xboole_0(B_48,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_152])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_99,plain,(
    ! [A_4,B_48] : k9_subset_1(A_4,B_48,A_4) = k3_xboole_0(B_48,A_4) ),
    inference(resolution,[status(thm)],[c_39,c_87])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_157,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(k9_subset_1(A_57,B_58,C_59),A_57)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_141,c_14])).

tff(c_265,plain,(
    ! [C_74,A_75,B_76] :
      ( v2_compts_1(C_74,A_75)
      | ~ v4_pre_topc(C_74,A_75)
      | ~ r1_tarski(C_74,B_76)
      | ~ v2_compts_1(B_76,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1541,plain,(
    ! [A_256,B_257,C_258,A_259] :
      ( v2_compts_1(k9_subset_1(A_256,B_257,C_258),A_259)
      | ~ v4_pre_topc(k9_subset_1(A_256,B_257,C_258),A_259)
      | ~ v2_compts_1(A_256,A_259)
      | ~ m1_subset_1(k9_subset_1(A_256,B_257,C_258),k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ m1_subset_1(A_256,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(A_256)) ) ),
    inference(resolution,[status(thm)],[c_157,c_265])).

tff(c_1584,plain,(
    ! [A_4,B_48,A_259] :
      ( v2_compts_1(k9_subset_1(A_4,B_48,A_4),A_259)
      | ~ v4_pre_topc(k9_subset_1(A_4,B_48,A_4),A_259)
      | ~ v2_compts_1(A_4,A_259)
      | ~ m1_subset_1(k3_xboole_0(B_48,A_4),k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ m1_subset_1(A_4,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_1541])).

tff(c_2892,plain,(
    ! [B_436,A_437,A_438] :
      ( v2_compts_1(k3_xboole_0(B_436,A_437),A_438)
      | ~ v4_pre_topc(k3_xboole_0(B_436,A_437),A_438)
      | ~ v2_compts_1(A_437,A_438)
      | ~ m1_subset_1(k3_xboole_0(B_436,A_437),k1_zfmisc_1(u1_struct_0(A_438)))
      | ~ m1_subset_1(A_437,k1_zfmisc_1(u1_struct_0(A_438)))
      | ~ l1_pre_topc(A_438)
      | ~ v2_pre_topc(A_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_99,c_99,c_1584])).

tff(c_2953,plain,(
    ! [B_48] :
      ( v2_compts_1(k3_xboole_0(B_48,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_48,'#skF_3'),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_161,c_2892])).

tff(c_3021,plain,(
    ! [B_439] :
      ( v2_compts_1(k3_xboole_0(B_439,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_439,'#skF_3'),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_26,c_2953])).

tff(c_3066,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_522,c_3021])).

tff(c_3090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_3066])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.71/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.10  
% 5.74/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.10  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k2_enumset1 > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 5.74/2.10  
% 5.74/2.10  %Foreground sorts:
% 5.74/2.10  
% 5.74/2.10  
% 5.74/2.10  %Background operators:
% 5.74/2.10  
% 5.74/2.10  
% 5.74/2.10  %Foreground operators:
% 5.74/2.10  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 5.74/2.10  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 5.74/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.74/2.10  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.74/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.74/2.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.74/2.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.74/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.74/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.74/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.74/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.74/2.10  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.74/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.74/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.74/2.10  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.74/2.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.74/2.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.74/2.10  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.74/2.10  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.74/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.74/2.10  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.74/2.10  
% 5.80/2.13  tff(f_111, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 5.80/2.13  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.80/2.13  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 5.80/2.13  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 5.80/2.13  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 5.80/2.13  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.80/2.13  tff(f_31, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.80/2.13  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.80/2.13  tff(f_92, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 5.80/2.13  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.80/2.13  tff(c_87, plain, (![A_47, B_48, C_49]: (k9_subset_1(A_47, B_48, C_49)=k3_xboole_0(B_48, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.80/2.13  tff(c_97, plain, (![B_48]: (k9_subset_1(u1_struct_0('#skF_1'), B_48, '#skF_3')=k3_xboole_0(B_48, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_87])).
% 5.80/2.13  tff(c_24, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.80/2.13  tff(c_109, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_24])).
% 5.80/2.13  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.80/2.13  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.80/2.13  tff(c_30, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.80/2.13  tff(c_28, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.80/2.13  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.80/2.13  tff(c_172, plain, (![B_62, A_63]: (v4_pre_topc(B_62, A_63) | ~v2_compts_1(B_62, A_63) | ~v8_pre_topc(A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.80/2.13  tff(c_190, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_172])).
% 5.80/2.13  tff(c_203, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_28, c_190])).
% 5.80/2.13  tff(c_26, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.80/2.13  tff(c_187, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_172])).
% 5.80/2.13  tff(c_200, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_26, c_187])).
% 5.80/2.13  tff(c_382, plain, (![A_94, B_95, C_96]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_94), B_95, C_96), A_94) | ~v4_pre_topc(C_96, A_94) | ~v4_pre_topc(B_95, A_94) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.80/2.13  tff(c_395, plain, (![B_48]: (v4_pre_topc(k3_xboole_0(B_48, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_48, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_382])).
% 5.80/2.13  tff(c_470, plain, (![B_104]: (v4_pre_topc(k3_xboole_0(B_104, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_104, '#skF_1') | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_200, c_395])).
% 5.80/2.13  tff(c_504, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_470])).
% 5.80/2.13  tff(c_522, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_504])).
% 5.80/2.13  tff(c_141, plain, (![A_57, B_58, C_59]: (m1_subset_1(k9_subset_1(A_57, B_58, C_59), k1_zfmisc_1(A_57)) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.80/2.13  tff(c_152, plain, (![B_48]: (m1_subset_1(k3_xboole_0(B_48, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_97, c_141])).
% 5.80/2.13  tff(c_161, plain, (![B_48]: (m1_subset_1(k3_xboole_0(B_48, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_152])).
% 5.80/2.13  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.80/2.13  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.80/2.13  tff(c_39, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 5.80/2.13  tff(c_99, plain, (![A_4, B_48]: (k9_subset_1(A_4, B_48, A_4)=k3_xboole_0(B_48, A_4))), inference(resolution, [status(thm)], [c_39, c_87])).
% 5.80/2.13  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.80/2.13  tff(c_157, plain, (![A_57, B_58, C_59]: (r1_tarski(k9_subset_1(A_57, B_58, C_59), A_57) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_141, c_14])).
% 5.80/2.13  tff(c_265, plain, (![C_74, A_75, B_76]: (v2_compts_1(C_74, A_75) | ~v4_pre_topc(C_74, A_75) | ~r1_tarski(C_74, B_76) | ~v2_compts_1(B_76, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.80/2.13  tff(c_1541, plain, (![A_256, B_257, C_258, A_259]: (v2_compts_1(k9_subset_1(A_256, B_257, C_258), A_259) | ~v4_pre_topc(k9_subset_1(A_256, B_257, C_258), A_259) | ~v2_compts_1(A_256, A_259) | ~m1_subset_1(k9_subset_1(A_256, B_257, C_258), k1_zfmisc_1(u1_struct_0(A_259))) | ~m1_subset_1(A_256, k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | ~m1_subset_1(C_258, k1_zfmisc_1(A_256)))), inference(resolution, [status(thm)], [c_157, c_265])).
% 5.80/2.13  tff(c_1584, plain, (![A_4, B_48, A_259]: (v2_compts_1(k9_subset_1(A_4, B_48, A_4), A_259) | ~v4_pre_topc(k9_subset_1(A_4, B_48, A_4), A_259) | ~v2_compts_1(A_4, A_259) | ~m1_subset_1(k3_xboole_0(B_48, A_4), k1_zfmisc_1(u1_struct_0(A_259))) | ~m1_subset_1(A_4, k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | ~m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_1541])).
% 5.80/2.13  tff(c_2892, plain, (![B_436, A_437, A_438]: (v2_compts_1(k3_xboole_0(B_436, A_437), A_438) | ~v4_pre_topc(k3_xboole_0(B_436, A_437), A_438) | ~v2_compts_1(A_437, A_438) | ~m1_subset_1(k3_xboole_0(B_436, A_437), k1_zfmisc_1(u1_struct_0(A_438))) | ~m1_subset_1(A_437, k1_zfmisc_1(u1_struct_0(A_438))) | ~l1_pre_topc(A_438) | ~v2_pre_topc(A_438))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_99, c_99, c_1584])).
% 5.80/2.13  tff(c_2953, plain, (![B_48]: (v2_compts_1(k3_xboole_0(B_48, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_48, '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_161, c_2892])).
% 5.80/2.13  tff(c_3021, plain, (![B_439]: (v2_compts_1(k3_xboole_0(B_439, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_439, '#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_26, c_2953])).
% 5.80/2.13  tff(c_3066, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_522, c_3021])).
% 5.80/2.13  tff(c_3090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_3066])).
% 5.80/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.13  
% 5.80/2.13  Inference rules
% 5.80/2.13  ----------------------
% 5.80/2.13  #Ref     : 0
% 5.80/2.13  #Sup     : 642
% 5.80/2.13  #Fact    : 0
% 5.80/2.13  #Define  : 0
% 5.80/2.13  #Split   : 1
% 5.80/2.13  #Chain   : 0
% 5.80/2.13  #Close   : 0
% 5.80/2.13  
% 5.80/2.13  Ordering : KBO
% 5.80/2.13  
% 5.80/2.13  Simplification rules
% 5.80/2.13  ----------------------
% 5.80/2.13  #Subsume      : 66
% 5.80/2.13  #Demod        : 1002
% 5.80/2.13  #Tautology    : 180
% 5.80/2.13  #SimpNegUnit  : 1
% 5.80/2.13  #BackRed      : 1
% 5.80/2.13  
% 5.80/2.13  #Partial instantiations: 0
% 5.80/2.13  #Strategies tried      : 1
% 5.80/2.13  
% 5.80/2.13  Timing (in seconds)
% 5.80/2.13  ----------------------
% 5.80/2.13  Preprocessing        : 0.32
% 5.80/2.13  Parsing              : 0.17
% 5.80/2.13  CNF conversion       : 0.02
% 5.80/2.13  Main loop            : 1.02
% 5.80/2.13  Inferencing          : 0.35
% 5.80/2.13  Reduction            : 0.41
% 5.80/2.13  Demodulation         : 0.33
% 5.80/2.13  BG Simplification    : 0.04
% 5.80/2.13  Subsumption          : 0.16
% 5.80/2.13  Abstraction          : 0.06
% 5.80/2.13  MUC search           : 0.00
% 5.80/2.14  Cooper               : 0.00
% 5.80/2.14  Total                : 1.39
% 5.80/2.14  Index Insertion      : 0.00
% 5.80/2.14  Index Deletion       : 0.00
% 5.80/2.14  Index Matching       : 0.00
% 5.80/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
