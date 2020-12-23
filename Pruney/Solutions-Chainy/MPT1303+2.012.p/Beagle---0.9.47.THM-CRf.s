%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:48 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  88 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).

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

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_59,plain,(
    ! [A_33,B_34,C_35] :
      ( k7_subset_1(A_33,B_34,C_35) = k4_xboole_0(B_34,C_35)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [C_35] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_35) = k4_xboole_0('#skF_2',C_35) ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_102,plain,(
    ! [A_42,B_43,C_44] :
      ( m1_subset_1(k7_subset_1(A_42,B_43,C_44),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_109,plain,(
    ! [C_35] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_102])).

tff(c_116,plain,(
    ! [C_35] : m1_subset_1(k4_xboole_0('#skF_2',C_35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_109])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_221,plain,(
    ! [B_52,A_53,C_54] :
      ( v1_tops_2(B_52,A_53)
      | ~ v1_tops_2(C_54,A_53)
      | ~ r1_tarski(B_52,C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_630,plain,(
    ! [A_93,B_94,A_95] :
      ( v1_tops_2(k4_xboole_0(A_93,B_94),A_95)
      | ~ v1_tops_2(A_93,A_95)
      | ~ m1_subset_1(A_93,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_95))))
      | ~ m1_subset_1(k4_xboole_0(A_93,B_94),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_95))))
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_2,c_221])).

tff(c_648,plain,(
    ! [C_35] :
      ( v1_tops_2(k4_xboole_0('#skF_2',C_35),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_116,c_630])).

tff(c_679,plain,(
    ! [C_96] : v1_tops_2(k4_xboole_0('#skF_2',C_96),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_648])).

tff(c_691,plain,(
    ! [B_4] : v1_tops_2(k3_xboole_0('#skF_2',B_4),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_679])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,(
    ! [A_38,B_39,C_40] :
      ( k9_subset_1(A_38,B_39,C_40) = k3_xboole_0(B_39,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    ! [B_39] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_39,'#skF_3') = k3_xboole_0(B_39,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_85])).

tff(c_14,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_92,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_14])).

tff(c_694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.43  
% 2.98/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.43  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.98/1.43  
% 2.98/1.43  %Foreground sorts:
% 2.98/1.43  
% 2.98/1.43  
% 2.98/1.43  %Background operators:
% 2.98/1.43  
% 2.98/1.43  
% 2.98/1.43  %Foreground operators:
% 2.98/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.43  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.98/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.98/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.43  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.98/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.98/1.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.98/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.43  
% 2.98/1.44  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.98/1.44  tff(f_68, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_tops_2)).
% 2.98/1.44  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.98/1.44  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 2.98/1.44  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.98/1.45  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tops_2)).
% 2.98/1.45  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.98/1.45  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.98/1.45  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.45  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.45  tff(c_16, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.45  tff(c_59, plain, (![A_33, B_34, C_35]: (k7_subset_1(A_33, B_34, C_35)=k4_xboole_0(B_34, C_35) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.45  tff(c_65, plain, (![C_35]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_35)=k4_xboole_0('#skF_2', C_35))), inference(resolution, [status(thm)], [c_20, c_59])).
% 2.98/1.45  tff(c_102, plain, (![A_42, B_43, C_44]: (m1_subset_1(k7_subset_1(A_42, B_43, C_44), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.98/1.45  tff(c_109, plain, (![C_35]: (m1_subset_1(k4_xboole_0('#skF_2', C_35), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_65, c_102])).
% 2.98/1.45  tff(c_116, plain, (![C_35]: (m1_subset_1(k4_xboole_0('#skF_2', C_35), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_109])).
% 2.98/1.45  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.98/1.45  tff(c_221, plain, (![B_52, A_53, C_54]: (v1_tops_2(B_52, A_53) | ~v1_tops_2(C_54, A_53) | ~r1_tarski(B_52, C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.98/1.45  tff(c_630, plain, (![A_93, B_94, A_95]: (v1_tops_2(k4_xboole_0(A_93, B_94), A_95) | ~v1_tops_2(A_93, A_95) | ~m1_subset_1(A_93, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_95)))) | ~m1_subset_1(k4_xboole_0(A_93, B_94), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_95)))) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_2, c_221])).
% 2.98/1.45  tff(c_648, plain, (![C_35]: (v1_tops_2(k4_xboole_0('#skF_2', C_35), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_116, c_630])).
% 2.98/1.45  tff(c_679, plain, (![C_96]: (v1_tops_2(k4_xboole_0('#skF_2', C_96), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_648])).
% 2.98/1.45  tff(c_691, plain, (![B_4]: (v1_tops_2(k3_xboole_0('#skF_2', B_4), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_679])).
% 2.98/1.45  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.45  tff(c_85, plain, (![A_38, B_39, C_40]: (k9_subset_1(A_38, B_39, C_40)=k3_xboole_0(B_39, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.45  tff(c_90, plain, (![B_39]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_39, '#skF_3')=k3_xboole_0(B_39, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_85])).
% 2.98/1.45  tff(c_14, plain, (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.45  tff(c_92, plain, (~v1_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_14])).
% 2.98/1.45  tff(c_694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_691, c_92])).
% 2.98/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.45  
% 2.98/1.45  Inference rules
% 2.98/1.45  ----------------------
% 2.98/1.45  #Ref     : 0
% 2.98/1.45  #Sup     : 162
% 2.98/1.45  #Fact    : 0
% 2.98/1.45  #Define  : 0
% 2.98/1.45  #Split   : 0
% 2.98/1.45  #Chain   : 0
% 2.98/1.45  #Close   : 0
% 2.98/1.45  
% 2.98/1.45  Ordering : KBO
% 2.98/1.45  
% 2.98/1.45  Simplification rules
% 2.98/1.45  ----------------------
% 2.98/1.45  #Subsume      : 0
% 2.98/1.45  #Demod        : 82
% 2.98/1.45  #Tautology    : 54
% 2.98/1.45  #SimpNegUnit  : 0
% 2.98/1.45  #BackRed      : 2
% 2.98/1.45  
% 2.98/1.45  #Partial instantiations: 0
% 2.98/1.45  #Strategies tried      : 1
% 2.98/1.45  
% 2.98/1.45  Timing (in seconds)
% 2.98/1.45  ----------------------
% 2.98/1.45  Preprocessing        : 0.28
% 2.98/1.45  Parsing              : 0.15
% 2.98/1.45  CNF conversion       : 0.02
% 2.98/1.45  Main loop            : 0.35
% 2.98/1.45  Inferencing          : 0.13
% 2.98/1.45  Reduction            : 0.12
% 2.98/1.45  Demodulation         : 0.09
% 2.98/1.45  BG Simplification    : 0.02
% 2.98/1.45  Subsumption          : 0.05
% 2.98/1.45  Abstraction          : 0.03
% 2.98/1.45  MUC search           : 0.00
% 2.98/1.45  Cooper               : 0.00
% 2.98/1.45  Total                : 0.66
% 2.98/1.45  Index Insertion      : 0.00
% 2.98/1.45  Index Deletion       : 0.00
% 2.98/1.45  Index Matching       : 0.00
% 2.98/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
