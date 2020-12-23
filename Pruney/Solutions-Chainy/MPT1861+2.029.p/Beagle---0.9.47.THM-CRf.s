%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:13 EST 2020

% Result     : Theorem 12.36s
% Output     : CNFRefutation 12.36s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 105 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 219 expanded)
%              Number of equality atoms :   10 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_245,plain,(
    ! [A_73,B_74,C_75] :
      ( k9_subset_1(A_73,B_74,C_75) = k3_xboole_0(B_74,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_258,plain,(
    ! [B_74] : k9_subset_1(u1_struct_0('#skF_1'),B_74,'#skF_3') = k3_xboole_0(B_74,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_245])).

tff(c_22,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_261,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_22])).

tff(c_24,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_43,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_262,plain,(
    ! [B_76] : k9_subset_1(u1_struct_0('#skF_1'),B_76,'#skF_3') = k3_xboole_0(B_76,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_245])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k9_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_271,plain,(
    ! [B_76] :
      ( m1_subset_1(k3_xboole_0(B_76,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_10])).

tff(c_279,plain,(
    ! [B_76] : m1_subset_1(k3_xboole_0(B_76,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_271])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_341,plain,(
    ! [C_84,A_85,B_86] :
      ( v2_tex_2(C_84,A_85)
      | ~ v2_tex_2(B_86,A_85)
      | ~ r1_tarski(C_84,B_86)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1051,plain,(
    ! [A_148,B_149,A_150] :
      ( v2_tex_2(k3_xboole_0(A_148,B_149),A_150)
      | ~ v2_tex_2(A_148,A_150)
      | ~ m1_subset_1(k3_xboole_0(A_148,B_149),k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ m1_subset_1(A_148,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(resolution,[status(thm)],[c_2,c_341])).

tff(c_1060,plain,(
    ! [B_76] :
      ( v2_tex_2(k3_xboole_0(B_76,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_76,'#skF_1')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_279,c_1051])).

tff(c_5473,plain,(
    ! [B_417] :
      ( v2_tex_2(k3_xboole_0(B_417,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_417,'#skF_1')
      | ~ m1_subset_1(B_417,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1060])).

tff(c_5513,plain,
    ( v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_5473])).

tff(c_5531,plain,(
    v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_5513])).

tff(c_5533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_5531])).

tff(c_5534,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_5737,plain,(
    ! [A_458,B_459,C_460] :
      ( k9_subset_1(A_458,B_459,C_460) = k3_xboole_0(B_459,C_460)
      | ~ m1_subset_1(C_460,k1_zfmisc_1(A_458)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5754,plain,(
    ! [B_461] : k9_subset_1(u1_struct_0('#skF_1'),B_461,'#skF_3') = k3_xboole_0(B_461,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_5737])).

tff(c_5763,plain,(
    ! [B_461] :
      ( m1_subset_1(k3_xboole_0(B_461,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5754,c_10])).

tff(c_5771,plain,(
    ! [B_461] : m1_subset_1(k3_xboole_0(B_461,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5763])).

tff(c_6,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_5785,plain,(
    ! [A_463,B_464] : k9_subset_1(A_463,B_464,A_463) = k3_xboole_0(B_464,A_463) ),
    inference(resolution,[status(thm)],[c_31,c_5737])).

tff(c_5689,plain,(
    ! [A_448,B_449,C_450] :
      ( m1_subset_1(k9_subset_1(A_448,B_449,C_450),k1_zfmisc_1(A_448))
      | ~ m1_subset_1(C_450,k1_zfmisc_1(A_448)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5693,plain,(
    ! [A_448,B_449,C_450] :
      ( r1_tarski(k9_subset_1(A_448,B_449,C_450),A_448)
      | ~ m1_subset_1(C_450,k1_zfmisc_1(A_448)) ) ),
    inference(resolution,[status(thm)],[c_5689,c_16])).

tff(c_5791,plain,(
    ! [B_464,A_463] :
      ( r1_tarski(k3_xboole_0(B_464,A_463),A_463)
      | ~ m1_subset_1(A_463,k1_zfmisc_1(A_463)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5785,c_5693])).

tff(c_5800,plain,(
    ! [B_464,A_463] : r1_tarski(k3_xboole_0(B_464,A_463),A_463) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_5791])).

tff(c_5833,plain,(
    ! [C_469,A_470,B_471] :
      ( v2_tex_2(C_469,A_470)
      | ~ v2_tex_2(B_471,A_470)
      | ~ r1_tarski(C_469,B_471)
      | ~ m1_subset_1(C_469,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ m1_subset_1(B_471,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ l1_pre_topc(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_27804,plain,(
    ! [B_1438,A_1439,A_1440] :
      ( v2_tex_2(k3_xboole_0(B_1438,A_1439),A_1440)
      | ~ v2_tex_2(A_1439,A_1440)
      | ~ m1_subset_1(k3_xboole_0(B_1438,A_1439),k1_zfmisc_1(u1_struct_0(A_1440)))
      | ~ m1_subset_1(A_1439,k1_zfmisc_1(u1_struct_0(A_1440)))
      | ~ l1_pre_topc(A_1440) ) ),
    inference(resolution,[status(thm)],[c_5800,c_5833])).

tff(c_27858,plain,(
    ! [B_461] :
      ( v2_tex_2(k3_xboole_0(B_461,'#skF_3'),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_5771,c_27804])).

tff(c_27909,plain,(
    ! [B_461] : v2_tex_2(k3_xboole_0(B_461,'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_5534,c_27858])).

tff(c_5750,plain,(
    ! [B_459] : k9_subset_1(u1_struct_0('#skF_1'),B_459,'#skF_3') = k3_xboole_0(B_459,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_5737])).

tff(c_5753,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5750,c_22])).

tff(c_27921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27909,c_5753])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:29:46 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.36/5.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.36/5.97  
% 12.36/5.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.36/5.97  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 12.36/5.97  
% 12.36/5.97  %Foreground sorts:
% 12.36/5.97  
% 12.36/5.97  
% 12.36/5.97  %Background operators:
% 12.36/5.97  
% 12.36/5.97  
% 12.36/5.97  %Foreground operators:
% 12.36/5.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.36/5.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.36/5.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.36/5.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.36/5.97  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 12.36/5.97  tff('#skF_2', type, '#skF_2': $i).
% 12.36/5.97  tff('#skF_3', type, '#skF_3': $i).
% 12.36/5.97  tff('#skF_1', type, '#skF_1': $i).
% 12.36/5.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.36/5.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.36/5.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.36/5.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.36/5.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.36/5.97  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.36/5.97  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 12.36/5.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.36/5.97  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.36/5.97  
% 12.36/5.98  tff(f_80, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 12.36/5.98  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 12.36/5.98  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 12.36/5.98  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 12.36/5.98  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 12.36/5.98  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 12.36/5.98  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 12.36/5.98  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.36/5.98  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.36/5.98  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.36/5.98  tff(c_245, plain, (![A_73, B_74, C_75]: (k9_subset_1(A_73, B_74, C_75)=k3_xboole_0(B_74, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.36/5.98  tff(c_258, plain, (![B_74]: (k9_subset_1(u1_struct_0('#skF_1'), B_74, '#skF_3')=k3_xboole_0(B_74, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_245])).
% 12.36/5.98  tff(c_22, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.36/5.98  tff(c_261, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_22])).
% 12.36/5.98  tff(c_24, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.36/5.98  tff(c_43, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 12.36/5.98  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.36/5.98  tff(c_262, plain, (![B_76]: (k9_subset_1(u1_struct_0('#skF_1'), B_76, '#skF_3')=k3_xboole_0(B_76, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_245])).
% 12.36/5.98  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k9_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.36/5.98  tff(c_271, plain, (![B_76]: (m1_subset_1(k3_xboole_0(B_76, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_262, c_10])).
% 12.36/5.98  tff(c_279, plain, (![B_76]: (m1_subset_1(k3_xboole_0(B_76, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_271])).
% 12.36/5.98  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.36/5.98  tff(c_341, plain, (![C_84, A_85, B_86]: (v2_tex_2(C_84, A_85) | ~v2_tex_2(B_86, A_85) | ~r1_tarski(C_84, B_86) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.36/5.98  tff(c_1051, plain, (![A_148, B_149, A_150]: (v2_tex_2(k3_xboole_0(A_148, B_149), A_150) | ~v2_tex_2(A_148, A_150) | ~m1_subset_1(k3_xboole_0(A_148, B_149), k1_zfmisc_1(u1_struct_0(A_150))) | ~m1_subset_1(A_148, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(resolution, [status(thm)], [c_2, c_341])).
% 12.36/5.98  tff(c_1060, plain, (![B_76]: (v2_tex_2(k3_xboole_0(B_76, '#skF_3'), '#skF_1') | ~v2_tex_2(B_76, '#skF_1') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_279, c_1051])).
% 12.36/5.98  tff(c_5473, plain, (![B_417]: (v2_tex_2(k3_xboole_0(B_417, '#skF_3'), '#skF_1') | ~v2_tex_2(B_417, '#skF_1') | ~m1_subset_1(B_417, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1060])).
% 12.36/5.98  tff(c_5513, plain, (v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_5473])).
% 12.36/5.98  tff(c_5531, plain, (v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_43, c_5513])).
% 12.36/5.98  tff(c_5533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_261, c_5531])).
% 12.36/5.98  tff(c_5534, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 12.36/5.98  tff(c_5737, plain, (![A_458, B_459, C_460]: (k9_subset_1(A_458, B_459, C_460)=k3_xboole_0(B_459, C_460) | ~m1_subset_1(C_460, k1_zfmisc_1(A_458)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.36/5.98  tff(c_5754, plain, (![B_461]: (k9_subset_1(u1_struct_0('#skF_1'), B_461, '#skF_3')=k3_xboole_0(B_461, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_5737])).
% 12.36/5.98  tff(c_5763, plain, (![B_461]: (m1_subset_1(k3_xboole_0(B_461, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_5754, c_10])).
% 12.36/5.98  tff(c_5771, plain, (![B_461]: (m1_subset_1(k3_xboole_0(B_461, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_5763])).
% 12.36/5.98  tff(c_6, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.36/5.98  tff(c_8, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.36/5.98  tff(c_31, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 12.36/5.98  tff(c_5785, plain, (![A_463, B_464]: (k9_subset_1(A_463, B_464, A_463)=k3_xboole_0(B_464, A_463))), inference(resolution, [status(thm)], [c_31, c_5737])).
% 12.36/5.98  tff(c_5689, plain, (![A_448, B_449, C_450]: (m1_subset_1(k9_subset_1(A_448, B_449, C_450), k1_zfmisc_1(A_448)) | ~m1_subset_1(C_450, k1_zfmisc_1(A_448)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.36/5.98  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.36/5.98  tff(c_5693, plain, (![A_448, B_449, C_450]: (r1_tarski(k9_subset_1(A_448, B_449, C_450), A_448) | ~m1_subset_1(C_450, k1_zfmisc_1(A_448)))), inference(resolution, [status(thm)], [c_5689, c_16])).
% 12.36/5.98  tff(c_5791, plain, (![B_464, A_463]: (r1_tarski(k3_xboole_0(B_464, A_463), A_463) | ~m1_subset_1(A_463, k1_zfmisc_1(A_463)))), inference(superposition, [status(thm), theory('equality')], [c_5785, c_5693])).
% 12.36/5.98  tff(c_5800, plain, (![B_464, A_463]: (r1_tarski(k3_xboole_0(B_464, A_463), A_463))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_5791])).
% 12.36/5.98  tff(c_5833, plain, (![C_469, A_470, B_471]: (v2_tex_2(C_469, A_470) | ~v2_tex_2(B_471, A_470) | ~r1_tarski(C_469, B_471) | ~m1_subset_1(C_469, k1_zfmisc_1(u1_struct_0(A_470))) | ~m1_subset_1(B_471, k1_zfmisc_1(u1_struct_0(A_470))) | ~l1_pre_topc(A_470))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.36/5.98  tff(c_27804, plain, (![B_1438, A_1439, A_1440]: (v2_tex_2(k3_xboole_0(B_1438, A_1439), A_1440) | ~v2_tex_2(A_1439, A_1440) | ~m1_subset_1(k3_xboole_0(B_1438, A_1439), k1_zfmisc_1(u1_struct_0(A_1440))) | ~m1_subset_1(A_1439, k1_zfmisc_1(u1_struct_0(A_1440))) | ~l1_pre_topc(A_1440))), inference(resolution, [status(thm)], [c_5800, c_5833])).
% 12.36/5.98  tff(c_27858, plain, (![B_461]: (v2_tex_2(k3_xboole_0(B_461, '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_5771, c_27804])).
% 12.36/5.98  tff(c_27909, plain, (![B_461]: (v2_tex_2(k3_xboole_0(B_461, '#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_5534, c_27858])).
% 12.36/5.98  tff(c_5750, plain, (![B_459]: (k9_subset_1(u1_struct_0('#skF_1'), B_459, '#skF_3')=k3_xboole_0(B_459, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_5737])).
% 12.36/5.98  tff(c_5753, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5750, c_22])).
% 12.36/5.98  tff(c_27921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27909, c_5753])).
% 12.36/5.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.36/5.98  
% 12.36/5.98  Inference rules
% 12.36/5.98  ----------------------
% 12.36/5.98  #Ref     : 0
% 12.36/5.98  #Sup     : 5967
% 12.36/5.98  #Fact    : 0
% 12.36/5.98  #Define  : 0
% 12.36/5.98  #Split   : 2
% 12.36/5.98  #Chain   : 0
% 12.36/5.98  #Close   : 0
% 12.36/5.98  
% 12.36/5.98  Ordering : KBO
% 12.36/5.98  
% 12.36/5.98  Simplification rules
% 12.36/5.98  ----------------------
% 12.36/5.98  #Subsume      : 321
% 12.36/5.98  #Demod        : 1435
% 12.36/5.98  #Tautology    : 816
% 12.36/5.98  #SimpNegUnit  : 8
% 12.36/5.98  #BackRed      : 4
% 12.36/5.98  
% 12.36/5.98  #Partial instantiations: 0
% 12.36/5.98  #Strategies tried      : 1
% 12.36/5.98  
% 12.36/5.98  Timing (in seconds)
% 12.36/5.98  ----------------------
% 12.36/5.99  Preprocessing        : 0.30
% 12.36/5.99  Parsing              : 0.16
% 12.36/5.99  CNF conversion       : 0.02
% 12.36/5.99  Main loop            : 4.94
% 12.36/5.99  Inferencing          : 0.94
% 12.36/5.99  Reduction            : 1.81
% 12.36/5.99  Demodulation         : 1.53
% 12.36/5.99  BG Simplification    : 0.13
% 12.36/5.99  Subsumption          : 1.74
% 12.36/5.99  Abstraction          : 0.15
% 12.36/5.99  MUC search           : 0.00
% 12.36/5.99  Cooper               : 0.00
% 12.36/5.99  Total                : 5.27
% 12.36/5.99  Index Insertion      : 0.00
% 12.36/5.99  Index Deletion       : 0.00
% 12.36/5.99  Index Matching       : 0.00
% 12.36/5.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
