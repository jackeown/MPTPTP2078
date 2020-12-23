%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:52 EST 2020

% Result     : Theorem 9.49s
% Output     : CNFRefutation 9.49s
% Verified   : 
% Statistics : Number of formulae       :   58 (  77 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 120 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tops_2)).

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

tff(f_65,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_193,plain,(
    ! [A_55,B_56,C_57] :
      ( k9_subset_1(A_55,B_56,C_57) = k3_xboole_0(B_56,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_345,plain,(
    ! [B_73] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_73,'#skF_2') = k3_xboole_0(B_73,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_193])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k9_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_354,plain,(
    ! [B_73] :
      ( m1_subset_1(k3_xboole_0(B_73,'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_10])).

tff(c_362,plain,(
    ! [B_73] : m1_subset_1(k3_xboole_0(B_73,'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_354])).

tff(c_6,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_209,plain,(
    ! [A_58,B_59] : k9_subset_1(A_58,B_59,A_58) = k3_xboole_0(B_59,A_58) ),
    inference(resolution,[status(thm)],[c_31,c_193])).

tff(c_184,plain,(
    ! [A_49,B_50,C_51] :
      ( m1_subset_1(k9_subset_1(A_49,B_50,C_51),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_188,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(k9_subset_1(A_49,B_50,C_51),A_49)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_184,c_16])).

tff(c_215,plain,(
    ! [B_59,A_58] :
      ( r1_tarski(k3_xboole_0(B_59,A_58),A_58)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(A_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_188])).

tff(c_247,plain,(
    ! [B_63,A_64] : r1_tarski(k3_xboole_0(B_63,A_64),A_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_215])).

tff(c_20,plain,(
    ! [B_22,A_18,C_24] :
      ( v2_tops_2(B_22,A_18)
      | ~ v2_tops_2(C_24,A_18)
      | ~ r1_tarski(B_22,C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18))))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18))))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_21225,plain,(
    ! [B_451,A_452,A_453] :
      ( v2_tops_2(k3_xboole_0(B_451,A_452),A_453)
      | ~ v2_tops_2(A_452,A_453)
      | ~ m1_subset_1(A_452,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_453))))
      | ~ m1_subset_1(k3_xboole_0(B_451,A_452),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_453))))
      | ~ l1_pre_topc(A_453) ) ),
    inference(resolution,[status(thm)],[c_247,c_20])).

tff(c_21364,plain,(
    ! [B_73] :
      ( v2_tops_2(k3_xboole_0(B_73,'#skF_2'),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_362,c_21225])).

tff(c_21448,plain,(
    ! [B_73] : v2_tops_2(k3_xboole_0(B_73,'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_21364])).

tff(c_4,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_94,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_109,plain,(
    ! [B_40,A_41] : k1_setfam_1(k2_tarski(B_40,A_41)) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_94])).

tff(c_14,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_115,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_14])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_207,plain,(
    ! [B_56] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_56,'#skF_3') = k3_xboole_0(B_56,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_193])).

tff(c_22,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_276,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_22])).

tff(c_277,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_276])).

tff(c_21459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21448,c_277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:31:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.49/4.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/4.11  
% 9.49/4.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/4.11  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 9.49/4.11  
% 9.49/4.11  %Foreground sorts:
% 9.49/4.11  
% 9.49/4.11  
% 9.49/4.11  %Background operators:
% 9.49/4.11  
% 9.49/4.11  
% 9.49/4.11  %Foreground operators:
% 9.49/4.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.49/4.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.49/4.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.49/4.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.49/4.11  tff('#skF_2', type, '#skF_2': $i).
% 9.49/4.11  tff('#skF_3', type, '#skF_3': $i).
% 9.49/4.11  tff('#skF_1', type, '#skF_1': $i).
% 9.49/4.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.49/4.11  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 9.49/4.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.49/4.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.49/4.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.49/4.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.49/4.11  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.49/4.11  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.49/4.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.49/4.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.49/4.11  
% 9.49/4.12  tff(f_78, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tops_2)).
% 9.49/4.12  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.49/4.12  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 9.49/4.12  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.49/4.12  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.49/4.12  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.49/4.12  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 9.49/4.12  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.49/4.12  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.49/4.12  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.49/4.12  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.49/4.12  tff(c_24, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.49/4.12  tff(c_193, plain, (![A_55, B_56, C_57]: (k9_subset_1(A_55, B_56, C_57)=k3_xboole_0(B_56, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.49/4.12  tff(c_345, plain, (![B_73]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_73, '#skF_2')=k3_xboole_0(B_73, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_193])).
% 9.49/4.12  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k9_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.49/4.12  tff(c_354, plain, (![B_73]: (m1_subset_1(k3_xboole_0(B_73, '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_345, c_10])).
% 9.49/4.12  tff(c_362, plain, (![B_73]: (m1_subset_1(k3_xboole_0(B_73, '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_354])).
% 9.49/4.12  tff(c_6, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.49/4.12  tff(c_8, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.49/4.12  tff(c_31, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 9.49/4.12  tff(c_209, plain, (![A_58, B_59]: (k9_subset_1(A_58, B_59, A_58)=k3_xboole_0(B_59, A_58))), inference(resolution, [status(thm)], [c_31, c_193])).
% 9.49/4.12  tff(c_184, plain, (![A_49, B_50, C_51]: (m1_subset_1(k9_subset_1(A_49, B_50, C_51), k1_zfmisc_1(A_49)) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.49/4.12  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.49/4.12  tff(c_188, plain, (![A_49, B_50, C_51]: (r1_tarski(k9_subset_1(A_49, B_50, C_51), A_49) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)))), inference(resolution, [status(thm)], [c_184, c_16])).
% 9.49/4.12  tff(c_215, plain, (![B_59, A_58]: (r1_tarski(k3_xboole_0(B_59, A_58), A_58) | ~m1_subset_1(A_58, k1_zfmisc_1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_209, c_188])).
% 9.49/4.12  tff(c_247, plain, (![B_63, A_64]: (r1_tarski(k3_xboole_0(B_63, A_64), A_64))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_215])).
% 9.49/4.12  tff(c_20, plain, (![B_22, A_18, C_24]: (v2_tops_2(B_22, A_18) | ~v2_tops_2(C_24, A_18) | ~r1_tarski(B_22, C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18)))) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18)))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.49/4.12  tff(c_21225, plain, (![B_451, A_452, A_453]: (v2_tops_2(k3_xboole_0(B_451, A_452), A_453) | ~v2_tops_2(A_452, A_453) | ~m1_subset_1(A_452, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_453)))) | ~m1_subset_1(k3_xboole_0(B_451, A_452), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_453)))) | ~l1_pre_topc(A_453))), inference(resolution, [status(thm)], [c_247, c_20])).
% 9.49/4.12  tff(c_21364, plain, (![B_73]: (v2_tops_2(k3_xboole_0(B_73, '#skF_2'), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_362, c_21225])).
% 9.49/4.12  tff(c_21448, plain, (![B_73]: (v2_tops_2(k3_xboole_0(B_73, '#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_21364])).
% 9.49/4.12  tff(c_4, plain, (![B_5, A_4]: (k2_tarski(B_5, A_4)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.49/4.12  tff(c_94, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.49/4.12  tff(c_109, plain, (![B_40, A_41]: (k1_setfam_1(k2_tarski(B_40, A_41))=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_4, c_94])).
% 9.49/4.12  tff(c_14, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.49/4.12  tff(c_115, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_109, c_14])).
% 9.49/4.12  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.49/4.12  tff(c_207, plain, (![B_56]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_56, '#skF_3')=k3_xboole_0(B_56, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_193])).
% 9.49/4.12  tff(c_22, plain, (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.49/4.12  tff(c_276, plain, (~v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_22])).
% 9.49/4.12  tff(c_277, plain, (~v2_tops_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_276])).
% 9.49/4.12  tff(c_21459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21448, c_277])).
% 9.49/4.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/4.12  
% 9.49/4.12  Inference rules
% 9.49/4.12  ----------------------
% 9.49/4.12  #Ref     : 0
% 9.49/4.12  #Sup     : 4940
% 9.49/4.12  #Fact    : 0
% 9.49/4.12  #Define  : 0
% 9.49/4.12  #Split   : 1
% 9.49/4.12  #Chain   : 0
% 9.49/4.12  #Close   : 0
% 9.49/4.12  
% 9.49/4.12  Ordering : KBO
% 9.49/4.12  
% 9.49/4.12  Simplification rules
% 9.49/4.12  ----------------------
% 9.49/4.12  #Subsume      : 356
% 9.49/4.12  #Demod        : 3260
% 9.49/4.12  #Tautology    : 2512
% 9.49/4.12  #SimpNegUnit  : 0
% 9.49/4.12  #BackRed      : 2
% 9.49/4.12  
% 9.49/4.12  #Partial instantiations: 0
% 9.49/4.12  #Strategies tried      : 1
% 9.49/4.12  
% 9.49/4.12  Timing (in seconds)
% 9.49/4.12  ----------------------
% 9.49/4.12  Preprocessing        : 0.30
% 9.49/4.13  Parsing              : 0.16
% 9.49/4.13  CNF conversion       : 0.02
% 9.49/4.13  Main loop            : 3.08
% 9.49/4.13  Inferencing          : 0.63
% 9.49/4.13  Reduction            : 1.71
% 9.49/4.13  Demodulation         : 1.54
% 9.49/4.13  BG Simplification    : 0.08
% 9.49/4.13  Subsumption          : 0.49
% 9.49/4.13  Abstraction          : 0.11
% 9.49/4.13  MUC search           : 0.00
% 9.49/4.13  Cooper               : 0.00
% 9.49/4.13  Total                : 3.41
% 9.49/4.13  Index Insertion      : 0.00
% 9.49/4.13  Index Deletion       : 0.00
% 9.49/4.13  Index Matching       : 0.00
% 9.49/4.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
