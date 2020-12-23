%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:58 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   58 (  98 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 318 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_101,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_82,axiom,(
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

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_41,plain,(
    ! [A_32,B_33,C_34] :
      ( k9_subset_1(A_32,B_33,C_34) = k3_xboole_0(B_33,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [B_33] : k9_subset_1(u1_struct_0('#skF_1'),B_33,'#skF_3') = k3_xboole_0(B_33,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_16,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_57,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_16])).

tff(c_20,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_81,plain,(
    ! [B_40,A_41] :
      ( v4_pre_topc(B_40,A_41)
      | ~ v2_compts_1(B_40,A_41)
      | ~ v8_pre_topc(A_41)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_88,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_81])).

tff(c_95,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_20,c_88])).

tff(c_18,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_91,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_98,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_18,c_91])).

tff(c_159,plain,(
    ! [B_52,C_53,A_54] :
      ( v4_pre_topc(k3_xboole_0(B_52,C_53),A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ v4_pre_topc(C_53,A_54)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ v4_pre_topc(B_52,A_54)
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_172,plain,(
    ! [B_52] :
      ( v4_pre_topc(k3_xboole_0(B_52,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_52,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_159])).

tff(c_240,plain,(
    ! [B_60] :
      ( v4_pre_topc(k3_xboole_0(B_60,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_60,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_98,c_172])).

tff(c_259,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_240])).

tff(c_270,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_259])).

tff(c_67,plain,(
    ! [A_37,B_38,C_39] :
      ( m1_subset_1(k9_subset_1(A_37,B_38,C_39),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [B_33] :
      ( m1_subset_1(k3_xboole_0(B_33,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_67])).

tff(c_78,plain,(
    ! [B_33] : m1_subset_1(k3_xboole_0(B_33,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_72])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_274,plain,(
    ! [C_61,A_62,B_63] :
      ( v2_compts_1(C_61,A_62)
      | ~ v4_pre_topc(C_61,A_62)
      | ~ r1_tarski(C_61,B_63)
      | ~ v2_compts_1(B_63,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_566,plain,(
    ! [A_137,B_138,A_139] :
      ( v2_compts_1(k3_xboole_0(A_137,B_138),A_139)
      | ~ v4_pre_topc(k3_xboole_0(A_137,B_138),A_139)
      | ~ v2_compts_1(A_137,A_139)
      | ~ m1_subset_1(k3_xboole_0(A_137,B_138),k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(A_137,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_2,c_274])).

tff(c_587,plain,(
    ! [B_33] :
      ( v2_compts_1(k3_xboole_0(B_33,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_33,'#skF_3'),'#skF_1')
      | ~ v2_compts_1(B_33,'#skF_1')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_78,c_566])).

tff(c_615,plain,(
    ! [B_140] :
      ( v2_compts_1(k3_xboole_0(B_140,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_140,'#skF_3'),'#skF_1')
      | ~ v2_compts_1(B_140,'#skF_1')
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_587])).

tff(c_646,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_615])).

tff(c_661,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_270,c_646])).

tff(c_663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.51  
% 2.88/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.51  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.88/1.51  
% 2.88/1.51  %Foreground sorts:
% 2.88/1.51  
% 2.88/1.51  
% 2.88/1.51  %Background operators:
% 2.88/1.51  
% 2.88/1.51  
% 2.88/1.51  %Foreground operators:
% 2.88/1.51  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.88/1.51  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 2.88/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.88/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.88/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.88/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.88/1.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.88/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.88/1.51  
% 2.88/1.52  tff(f_101, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 2.88/1.52  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.88/1.52  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 2.88/1.52  tff(f_51, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tops_1)).
% 2.88/1.52  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.88/1.52  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.88/1.52  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 2.88/1.52  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.52  tff(c_41, plain, (![A_32, B_33, C_34]: (k9_subset_1(A_32, B_33, C_34)=k3_xboole_0(B_33, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.52  tff(c_47, plain, (![B_33]: (k9_subset_1(u1_struct_0('#skF_1'), B_33, '#skF_3')=k3_xboole_0(B_33, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_41])).
% 2.88/1.52  tff(c_16, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.52  tff(c_57, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_16])).
% 2.88/1.52  tff(c_20, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.52  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.52  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.52  tff(c_22, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.52  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.52  tff(c_81, plain, (![B_40, A_41]: (v4_pre_topc(B_40, A_41) | ~v2_compts_1(B_40, A_41) | ~v8_pre_topc(A_41) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.88/1.52  tff(c_88, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_81])).
% 2.88/1.52  tff(c_95, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_22, c_20, c_88])).
% 2.88/1.52  tff(c_18, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.52  tff(c_91, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_81])).
% 2.88/1.52  tff(c_98, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_22, c_18, c_91])).
% 2.88/1.52  tff(c_159, plain, (![B_52, C_53, A_54]: (v4_pre_topc(k3_xboole_0(B_52, C_53), A_54) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~v4_pre_topc(C_53, A_54) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_54))) | ~v4_pre_topc(B_52, A_54) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.88/1.52  tff(c_172, plain, (![B_52]: (v4_pre_topc(k3_xboole_0(B_52, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_52, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_159])).
% 2.88/1.52  tff(c_240, plain, (![B_60]: (v4_pre_topc(k3_xboole_0(B_60, '#skF_3'), '#skF_1') | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_60, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_98, c_172])).
% 2.88/1.52  tff(c_259, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_240])).
% 2.88/1.52  tff(c_270, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_259])).
% 2.88/1.52  tff(c_67, plain, (![A_37, B_38, C_39]: (m1_subset_1(k9_subset_1(A_37, B_38, C_39), k1_zfmisc_1(A_37)) | ~m1_subset_1(C_39, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.52  tff(c_72, plain, (![B_33]: (m1_subset_1(k3_xboole_0(B_33, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_47, c_67])).
% 2.88/1.52  tff(c_78, plain, (![B_33]: (m1_subset_1(k3_xboole_0(B_33, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_72])).
% 2.88/1.52  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.88/1.52  tff(c_274, plain, (![C_61, A_62, B_63]: (v2_compts_1(C_61, A_62) | ~v4_pre_topc(C_61, A_62) | ~r1_tarski(C_61, B_63) | ~v2_compts_1(B_63, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.88/1.52  tff(c_566, plain, (![A_137, B_138, A_139]: (v2_compts_1(k3_xboole_0(A_137, B_138), A_139) | ~v4_pre_topc(k3_xboole_0(A_137, B_138), A_139) | ~v2_compts_1(A_137, A_139) | ~m1_subset_1(k3_xboole_0(A_137, B_138), k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_subset_1(A_137, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139))), inference(resolution, [status(thm)], [c_2, c_274])).
% 2.88/1.52  tff(c_587, plain, (![B_33]: (v2_compts_1(k3_xboole_0(B_33, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_33, '#skF_3'), '#skF_1') | ~v2_compts_1(B_33, '#skF_1') | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_78, c_566])).
% 2.88/1.52  tff(c_615, plain, (![B_140]: (v2_compts_1(k3_xboole_0(B_140, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_140, '#skF_3'), '#skF_1') | ~v2_compts_1(B_140, '#skF_1') | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_587])).
% 2.88/1.52  tff(c_646, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_615])).
% 2.88/1.52  tff(c_661, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_270, c_646])).
% 2.88/1.52  tff(c_663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_661])).
% 2.88/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.52  
% 2.88/1.52  Inference rules
% 2.88/1.52  ----------------------
% 2.88/1.52  #Ref     : 0
% 2.88/1.52  #Sup     : 128
% 2.88/1.52  #Fact    : 0
% 2.88/1.52  #Define  : 0
% 2.88/1.52  #Split   : 0
% 2.88/1.52  #Chain   : 0
% 2.88/1.52  #Close   : 0
% 2.88/1.52  
% 2.88/1.52  Ordering : KBO
% 2.88/1.52  
% 2.88/1.52  Simplification rules
% 2.88/1.52  ----------------------
% 2.88/1.52  #Subsume      : 12
% 2.88/1.52  #Demod        : 159
% 2.88/1.52  #Tautology    : 24
% 2.88/1.52  #SimpNegUnit  : 1
% 2.88/1.52  #BackRed      : 1
% 2.88/1.52  
% 2.88/1.52  #Partial instantiations: 0
% 2.88/1.52  #Strategies tried      : 1
% 2.88/1.52  
% 2.88/1.52  Timing (in seconds)
% 2.88/1.52  ----------------------
% 2.88/1.52  Preprocessing        : 0.28
% 2.88/1.52  Parsing              : 0.15
% 2.88/1.52  CNF conversion       : 0.02
% 2.88/1.52  Main loop            : 0.36
% 2.88/1.52  Inferencing          : 0.14
% 2.88/1.52  Reduction            : 0.12
% 2.88/1.52  Demodulation         : 0.09
% 2.88/1.52  BG Simplification    : 0.02
% 2.88/1.52  Subsumption          : 0.06
% 2.88/1.53  Abstraction          : 0.02
% 2.88/1.53  MUC search           : 0.00
% 2.88/1.53  Cooper               : 0.00
% 2.88/1.53  Total                : 0.67
% 2.88/1.53  Index Insertion      : 0.00
% 2.88/1.53  Index Deletion       : 0.00
% 2.88/1.53  Index Matching       : 0.00
% 2.88/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
