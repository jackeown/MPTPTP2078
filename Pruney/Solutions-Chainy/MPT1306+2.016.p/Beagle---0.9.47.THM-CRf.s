%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:53 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   47 (  74 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 158 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

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

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_51,axiom,(
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
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [C_41,A_42,B_43] :
      ( m1_subset_1(C_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42))))
      | ~ r1_tarski(C_41,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42))))
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_93,plain,(
    ! [A_1,B_2,A_42] :
      ( m1_subset_1(k4_xboole_0(A_1,B_2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42))))
      | ~ m1_subset_1(A_1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42))))
      | ~ l1_struct_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_2,c_87])).

tff(c_160,plain,(
    ! [B_48,A_49,C_50] :
      ( v2_tops_2(B_48,A_49)
      | ~ v2_tops_2(C_50,A_49)
      | ~ r1_tarski(B_48,C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_49))))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_49))))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_246,plain,(
    ! [A_59,B_60,A_61] :
      ( v2_tops_2(k4_xboole_0(A_59,B_60),A_61)
      | ~ v2_tops_2(A_59,A_61)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61))))
      | ~ m1_subset_1(k4_xboole_0(A_59,B_60),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61))))
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_2,c_160])).

tff(c_271,plain,(
    ! [A_62,B_63,A_64] :
      ( v2_tops_2(k4_xboole_0(A_62,B_63),A_64)
      | ~ v2_tops_2(A_62,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_64))))
      | ~ l1_struct_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_93,c_246])).

tff(c_279,plain,(
    ! [B_63] :
      ( v2_tops_2(k4_xboole_0('#skF_2',B_63),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_271])).

tff(c_287,plain,(
    ! [B_63] :
      ( v2_tops_2(k4_xboole_0('#skF_2',B_63),'#skF_1')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_279])).

tff(c_288,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_292,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_288])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_292])).

tff(c_299,plain,(
    ! [B_65] : v2_tops_2(k4_xboole_0('#skF_2',B_65),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_319,plain,(
    ! [B_4] : v2_tops_2(k3_xboole_0('#skF_2',B_4),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_299])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [A_34,B_35,C_36] :
      ( k9_subset_1(A_34,B_35,C_36) = k3_xboole_0(B_35,C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_49,plain,(
    ! [B_35] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_35,'#skF_3') = k3_xboole_0(B_35,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_44])).

tff(c_14,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_51,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_14])).

tff(c_322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.26  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.26  
% 2.18/1.26  %Foreground sorts:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Background operators:
% 2.18/1.26  
% 2.18/1.26  
% 2.18/1.26  %Foreground operators:
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.18/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.26  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.18/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.26  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.18/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.26  
% 2.18/1.27  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.18/1.27  tff(f_74, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tops_2)).
% 2.18/1.27  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.18/1.27  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.18/1.27  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 2.18/1.27  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 2.18/1.27  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.18/1.27  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.27  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.27  tff(c_8, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.27  tff(c_16, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.27  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.27  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.27  tff(c_87, plain, (![C_41, A_42, B_43]: (m1_subset_1(C_41, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42)))) | ~r1_tarski(C_41, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42)))) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.18/1.27  tff(c_93, plain, (![A_1, B_2, A_42]: (m1_subset_1(k4_xboole_0(A_1, B_2), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42)))) | ~m1_subset_1(A_1, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42)))) | ~l1_struct_0(A_42))), inference(resolution, [status(thm)], [c_2, c_87])).
% 2.18/1.27  tff(c_160, plain, (![B_48, A_49, C_50]: (v2_tops_2(B_48, A_49) | ~v2_tops_2(C_50, A_49) | ~r1_tarski(B_48, C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_49)))) | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_49)))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.27  tff(c_246, plain, (![A_59, B_60, A_61]: (v2_tops_2(k4_xboole_0(A_59, B_60), A_61) | ~v2_tops_2(A_59, A_61) | ~m1_subset_1(A_59, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61)))) | ~m1_subset_1(k4_xboole_0(A_59, B_60), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61)))) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_2, c_160])).
% 2.18/1.27  tff(c_271, plain, (![A_62, B_63, A_64]: (v2_tops_2(k4_xboole_0(A_62, B_63), A_64) | ~v2_tops_2(A_62, A_64) | ~l1_pre_topc(A_64) | ~m1_subset_1(A_62, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_64)))) | ~l1_struct_0(A_64))), inference(resolution, [status(thm)], [c_93, c_246])).
% 2.18/1.27  tff(c_279, plain, (![B_63]: (v2_tops_2(k4_xboole_0('#skF_2', B_63), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_271])).
% 2.18/1.27  tff(c_287, plain, (![B_63]: (v2_tops_2(k4_xboole_0('#skF_2', B_63), '#skF_1') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_279])).
% 2.18/1.27  tff(c_288, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_287])).
% 2.18/1.27  tff(c_292, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_288])).
% 2.18/1.27  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_292])).
% 2.18/1.27  tff(c_299, plain, (![B_65]: (v2_tops_2(k4_xboole_0('#skF_2', B_65), '#skF_1'))), inference(splitRight, [status(thm)], [c_287])).
% 2.18/1.27  tff(c_319, plain, (![B_4]: (v2_tops_2(k3_xboole_0('#skF_2', B_4), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_299])).
% 2.18/1.27  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.27  tff(c_44, plain, (![A_34, B_35, C_36]: (k9_subset_1(A_34, B_35, C_36)=k3_xboole_0(B_35, C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.27  tff(c_49, plain, (![B_35]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_35, '#skF_3')=k3_xboole_0(B_35, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_44])).
% 2.18/1.27  tff(c_14, plain, (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.27  tff(c_51, plain, (~v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_14])).
% 2.18/1.27  tff(c_322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_319, c_51])).
% 2.18/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  Inference rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Ref     : 0
% 2.18/1.27  #Sup     : 74
% 2.18/1.27  #Fact    : 0
% 2.18/1.27  #Define  : 0
% 2.18/1.27  #Split   : 2
% 2.18/1.27  #Chain   : 0
% 2.18/1.27  #Close   : 0
% 2.18/1.27  
% 2.18/1.27  Ordering : KBO
% 2.18/1.27  
% 2.18/1.27  Simplification rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Subsume      : 3
% 2.18/1.27  #Demod        : 32
% 2.18/1.27  #Tautology    : 29
% 2.18/1.27  #SimpNegUnit  : 0
% 2.18/1.27  #BackRed      : 2
% 2.18/1.27  
% 2.18/1.27  #Partial instantiations: 0
% 2.18/1.27  #Strategies tried      : 1
% 2.18/1.27  
% 2.18/1.27  Timing (in seconds)
% 2.18/1.27  ----------------------
% 2.32/1.28  Preprocessing        : 0.29
% 2.32/1.28  Parsing              : 0.16
% 2.32/1.28  CNF conversion       : 0.02
% 2.32/1.28  Main loop            : 0.23
% 2.32/1.28  Inferencing          : 0.09
% 2.32/1.28  Reduction            : 0.08
% 2.32/1.28  Demodulation         : 0.06
% 2.32/1.28  BG Simplification    : 0.01
% 2.32/1.28  Subsumption          : 0.04
% 2.32/1.28  Abstraction          : 0.02
% 2.32/1.28  MUC search           : 0.00
% 2.32/1.28  Cooper               : 0.00
% 2.32/1.28  Total                : 0.55
% 2.32/1.28  Index Insertion      : 0.00
% 2.32/1.28  Index Deletion       : 0.00
% 2.32/1.28  Index Matching       : 0.00
% 2.32/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
