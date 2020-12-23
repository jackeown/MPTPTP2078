%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:52 EST 2020

% Result     : Theorem 22.77s
% Output     : CNFRefutation 22.77s
% Verified   : 
% Statistics : Number of formulae       :   57 (  94 expanded)
%              Number of leaves         :   25 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 166 expanded)
%              Number of equality atoms :   13 (  29 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tops_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_74,plain,(
    ! [A_42,B_43,C_44] :
      ( k9_subset_1(A_42,B_43,C_44) = k3_xboole_0(B_43,C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_119,plain,(
    ! [B_51] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_51,'#skF_2') = k3_xboole_0(B_51,'#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_74])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k9_subset_1(A_6,B_7,C_8),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_128,plain,(
    ! [B_51] :
      ( m1_subset_1(k3_xboole_0(B_51,'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_8])).

tff(c_136,plain,(
    ! [B_51] : m1_subset_1(k3_xboole_0(B_51,'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_128])).

tff(c_4,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_89,plain,(
    ! [A_5,B_43] : k9_subset_1(A_5,B_43,A_5) = k3_xboole_0(B_43,A_5) ),
    inference(resolution,[status(thm)],[c_29,c_74])).

tff(c_68,plain,(
    ! [A_36,B_37,C_38] :
      ( m1_subset_1(k9_subset_1(A_36,B_37,C_38),k1_zfmisc_1(A_36))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,(
    ! [A_36,B_37,C_38] :
      ( r1_tarski(k9_subset_1(A_36,B_37,C_38),A_36)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_36)) ) ),
    inference(resolution,[status(thm)],[c_68,c_14])).

tff(c_366,plain,(
    ! [B_64,A_65,C_66] :
      ( v2_tops_2(B_64,A_65)
      | ~ v2_tops_2(C_66,A_65)
      | ~ r1_tarski(B_64,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65))))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65))))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3744,plain,(
    ! [A_188,B_189,C_190,A_191] :
      ( v2_tops_2(k9_subset_1(A_188,B_189,C_190),A_191)
      | ~ v2_tops_2(A_188,A_191)
      | ~ m1_subset_1(A_188,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191))))
      | ~ m1_subset_1(k9_subset_1(A_188,B_189,C_190),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191))))
      | ~ l1_pre_topc(A_191)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(A_188)) ) ),
    inference(resolution,[status(thm)],[c_72,c_366])).

tff(c_3804,plain,(
    ! [A_5,B_43,A_191] :
      ( v2_tops_2(k9_subset_1(A_5,B_43,A_5),A_191)
      | ~ v2_tops_2(A_5,A_191)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191))))
      | ~ m1_subset_1(k3_xboole_0(B_43,A_5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191))))
      | ~ l1_pre_topc(A_191)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_3744])).

tff(c_44300,plain,(
    ! [B_1168,A_1169,A_1170] :
      ( v2_tops_2(k3_xboole_0(B_1168,A_1169),A_1170)
      | ~ v2_tops_2(A_1169,A_1170)
      | ~ m1_subset_1(A_1169,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1170))))
      | ~ m1_subset_1(k3_xboole_0(B_1168,A_1169),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1170))))
      | ~ l1_pre_topc(A_1170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_89,c_3804])).

tff(c_44425,plain,(
    ! [B_51] :
      ( v2_tops_2(k3_xboole_0(B_51,'#skF_2'),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_136,c_44300])).

tff(c_44486,plain,(
    ! [B_51] : v2_tops_2(k3_xboole_0(B_51,'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_44425])).

tff(c_87,plain,(
    ! [B_43] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_43,'#skF_2') = k3_xboole_0(B_43,'#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_74])).

tff(c_169,plain,(
    ! [A_56,C_57,B_58] :
      ( k9_subset_1(A_56,C_57,B_58) = k9_subset_1(A_56,B_58,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_179,plain,(
    ! [B_58] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_58,'#skF_2') = k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',B_58) ),
    inference(resolution,[status(thm)],[c_26,c_169])).

tff(c_249,plain,(
    ! [B_62] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',B_62) = k3_xboole_0(B_62,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_179])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_88,plain,(
    ! [B_43] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_43,'#skF_3') = k3_xboole_0(B_43,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_74])).

tff(c_256,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_88])).

tff(c_20,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_148,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_20])).

tff(c_292,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_148])).

tff(c_44493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44486,c_292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:08:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.77/14.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.77/14.05  
% 22.77/14.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.77/14.05  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 22.77/14.05  
% 22.77/14.05  %Foreground sorts:
% 22.77/14.05  
% 22.77/14.05  
% 22.77/14.05  %Background operators:
% 22.77/14.05  
% 22.77/14.05  
% 22.77/14.05  %Foreground operators:
% 22.77/14.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.77/14.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 22.77/14.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.77/14.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.77/14.05  tff('#skF_2', type, '#skF_2': $i).
% 22.77/14.05  tff('#skF_3', type, '#skF_3': $i).
% 22.77/14.05  tff('#skF_1', type, '#skF_1': $i).
% 22.77/14.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.77/14.05  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 22.77/14.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.77/14.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.77/14.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.77/14.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 22.77/14.05  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 22.77/14.05  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 22.77/14.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.77/14.05  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 22.77/14.05  
% 22.77/14.07  tff(f_74, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tops_2)).
% 22.77/14.07  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 22.77/14.07  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 22.77/14.07  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 22.77/14.07  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 22.77/14.07  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 22.77/14.07  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 22.77/14.07  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 22.77/14.07  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.77/14.07  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.77/14.07  tff(c_22, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.77/14.07  tff(c_74, plain, (![A_42, B_43, C_44]: (k9_subset_1(A_42, B_43, C_44)=k3_xboole_0(B_43, C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.77/14.07  tff(c_119, plain, (![B_51]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_51, '#skF_2')=k3_xboole_0(B_51, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_74])).
% 22.77/14.07  tff(c_8, plain, (![A_6, B_7, C_8]: (m1_subset_1(k9_subset_1(A_6, B_7, C_8), k1_zfmisc_1(A_6)) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.77/14.07  tff(c_128, plain, (![B_51]: (m1_subset_1(k3_xboole_0(B_51, '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_119, c_8])).
% 22.77/14.07  tff(c_136, plain, (![B_51]: (m1_subset_1(k3_xboole_0(B_51, '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_128])).
% 22.77/14.07  tff(c_4, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.77/14.07  tff(c_6, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.77/14.07  tff(c_29, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 22.77/14.07  tff(c_89, plain, (![A_5, B_43]: (k9_subset_1(A_5, B_43, A_5)=k3_xboole_0(B_43, A_5))), inference(resolution, [status(thm)], [c_29, c_74])).
% 22.77/14.07  tff(c_68, plain, (![A_36, B_37, C_38]: (m1_subset_1(k9_subset_1(A_36, B_37, C_38), k1_zfmisc_1(A_36)) | ~m1_subset_1(C_38, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.77/14.07  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 22.77/14.07  tff(c_72, plain, (![A_36, B_37, C_38]: (r1_tarski(k9_subset_1(A_36, B_37, C_38), A_36) | ~m1_subset_1(C_38, k1_zfmisc_1(A_36)))), inference(resolution, [status(thm)], [c_68, c_14])).
% 22.77/14.07  tff(c_366, plain, (![B_64, A_65, C_66]: (v2_tops_2(B_64, A_65) | ~v2_tops_2(C_66, A_65) | ~r1_tarski(B_64, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65)))) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65)))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.77/14.07  tff(c_3744, plain, (![A_188, B_189, C_190, A_191]: (v2_tops_2(k9_subset_1(A_188, B_189, C_190), A_191) | ~v2_tops_2(A_188, A_191) | ~m1_subset_1(A_188, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191)))) | ~m1_subset_1(k9_subset_1(A_188, B_189, C_190), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191)))) | ~l1_pre_topc(A_191) | ~m1_subset_1(C_190, k1_zfmisc_1(A_188)))), inference(resolution, [status(thm)], [c_72, c_366])).
% 22.77/14.07  tff(c_3804, plain, (![A_5, B_43, A_191]: (v2_tops_2(k9_subset_1(A_5, B_43, A_5), A_191) | ~v2_tops_2(A_5, A_191) | ~m1_subset_1(A_5, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191)))) | ~m1_subset_1(k3_xboole_0(B_43, A_5), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191)))) | ~l1_pre_topc(A_191) | ~m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_3744])).
% 22.77/14.07  tff(c_44300, plain, (![B_1168, A_1169, A_1170]: (v2_tops_2(k3_xboole_0(B_1168, A_1169), A_1170) | ~v2_tops_2(A_1169, A_1170) | ~m1_subset_1(A_1169, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1170)))) | ~m1_subset_1(k3_xboole_0(B_1168, A_1169), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1170)))) | ~l1_pre_topc(A_1170))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_89, c_3804])).
% 22.77/14.07  tff(c_44425, plain, (![B_51]: (v2_tops_2(k3_xboole_0(B_51, '#skF_2'), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_136, c_44300])).
% 22.77/14.07  tff(c_44486, plain, (![B_51]: (v2_tops_2(k3_xboole_0(B_51, '#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_44425])).
% 22.77/14.07  tff(c_87, plain, (![B_43]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_43, '#skF_2')=k3_xboole_0(B_43, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_74])).
% 22.77/14.07  tff(c_169, plain, (![A_56, C_57, B_58]: (k9_subset_1(A_56, C_57, B_58)=k9_subset_1(A_56, B_58, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.77/14.07  tff(c_179, plain, (![B_58]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_58, '#skF_2')=k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', B_58))), inference(resolution, [status(thm)], [c_26, c_169])).
% 22.77/14.07  tff(c_249, plain, (![B_62]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', B_62)=k3_xboole_0(B_62, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_179])).
% 22.77/14.07  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.77/14.07  tff(c_88, plain, (![B_43]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_43, '#skF_3')=k3_xboole_0(B_43, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_74])).
% 22.77/14.07  tff(c_256, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_249, c_88])).
% 22.77/14.07  tff(c_20, plain, (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.77/14.07  tff(c_148, plain, (~v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_20])).
% 22.77/14.07  tff(c_292, plain, (~v2_tops_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_148])).
% 22.77/14.07  tff(c_44493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44486, c_292])).
% 22.77/14.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.77/14.07  
% 22.77/14.07  Inference rules
% 22.77/14.07  ----------------------
% 22.77/14.07  #Ref     : 0
% 22.77/14.07  #Sup     : 12562
% 22.77/14.07  #Fact    : 0
% 22.77/14.07  #Define  : 0
% 22.77/14.07  #Split   : 1
% 22.77/14.07  #Chain   : 0
% 22.77/14.07  #Close   : 0
% 22.77/14.07  
% 22.77/14.07  Ordering : KBO
% 22.77/14.07  
% 22.77/14.07  Simplification rules
% 22.77/14.07  ----------------------
% 22.77/14.07  #Subsume      : 104
% 22.77/14.07  #Demod        : 4725
% 22.77/14.07  #Tautology    : 2425
% 22.77/14.07  #SimpNegUnit  : 0
% 22.77/14.07  #BackRed      : 6
% 22.77/14.07  
% 22.77/14.07  #Partial instantiations: 0
% 22.77/14.07  #Strategies tried      : 1
% 22.77/14.07  
% 22.77/14.07  Timing (in seconds)
% 22.77/14.07  ----------------------
% 22.77/14.07  Preprocessing        : 0.34
% 22.77/14.07  Parsing              : 0.18
% 22.77/14.07  CNF conversion       : 0.02
% 22.77/14.07  Main loop            : 12.91
% 22.77/14.07  Inferencing          : 1.55
% 22.77/14.07  Reduction            : 7.18
% 22.77/14.07  Demodulation         : 6.53
% 22.77/14.07  BG Simplification    : 0.26
% 22.77/14.07  Subsumption          : 3.22
% 22.77/14.07  Abstraction          : 0.34
% 22.77/14.07  MUC search           : 0.00
% 22.77/14.07  Cooper               : 0.00
% 22.77/14.07  Total                : 13.28
% 22.77/14.07  Index Insertion      : 0.00
% 22.77/14.07  Index Deletion       : 0.00
% 22.77/14.07  Index Matching       : 0.00
% 22.77/14.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
