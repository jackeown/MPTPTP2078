%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:07 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   56 (  99 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 215 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(k1_tops_2,type,(
    k1_tops_2: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( r1_tarski(B,k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)))
                 => r1_tarski(B,k5_setfam_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tops_2)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
     => m1_subset_1(k1_tops_2(A,B,C),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)),k5_setfam_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_2)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_282,plain,(
    ! [A_52,B_53] :
      ( u1_struct_0(k1_pre_topc(A_52,B_53)) = B_53
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_293,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_282])).

tff(c_298,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_293])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k5_setfam_1(A_31,B_32),k1_zfmisc_1(A_31))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k5_setfam_1(A_33,B_34),A_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(resolution,[status(thm)],[c_63,c_10])).

tff(c_78,plain,(
    ! [A_33,A_5] :
      ( r1_tarski(k5_setfam_1(A_33,A_5),A_33)
      | ~ r1_tarski(A_5,k1_zfmisc_1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_12,c_68])).

tff(c_88,plain,(
    ! [A_37,B_38] :
      ( u1_struct_0(k1_pre_topc(A_37,B_38)) = B_38
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_99,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_88])).

tff(c_104,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_99])).

tff(c_22,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_45,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,
    ( k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3')) = '#skF_2'
    | ~ r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_45])).

tff(c_87,plain,(
    ~ r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_105,plain,(
    ~ r1_tarski(k5_setfam_1('#skF_2',k1_tops_2('#skF_1','#skF_2','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_87])).

tff(c_120,plain,(
    ~ r1_tarski(k1_tops_2('#skF_1','#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_105])).

tff(c_121,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k1_tops_2(A_39,B_40,C_41),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_39,B_40)))))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39))))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_129,plain,(
    ! [C_41] :
      ( m1_subset_1(k1_tops_2('#skF_1','#skF_2',C_41),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_121])).

tff(c_241,plain,(
    ! [C_50] :
      ( m1_subset_1(k1_tops_2('#skF_1','#skF_2',C_50),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_129])).

tff(c_249,plain,(
    ! [C_51] :
      ( r1_tarski(k1_tops_2('#skF_1','#skF_2',C_51),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(resolution,[status(thm)],[c_241,c_10])).

tff(c_260,plain,(
    r1_tarski(k1_tops_2('#skF_1','#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_249])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_260])).

tff(c_267,plain,(
    k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_299,plain,(
    k5_setfam_1('#skF_2',k1_tops_2('#skF_1','#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_267])).

tff(c_489,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_69,B_70)),k1_tops_2(A_69,B_70,C_71)),k5_setfam_1(u1_struct_0(A_69),C_71))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69))))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_506,plain,(
    ! [C_71] :
      ( r1_tarski(k5_setfam_1('#skF_2',k1_tops_2('#skF_1','#skF_2',C_71)),k5_setfam_1(u1_struct_0('#skF_1'),C_71))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_489])).

tff(c_573,plain,(
    ! [C_78] :
      ( r1_tarski(k5_setfam_1('#skF_2',k1_tops_2('#skF_1','#skF_2',C_78)),k5_setfam_1(u1_struct_0('#skF_1'),C_78))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_506])).

tff(c_578,plain,
    ( r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_573])).

tff(c_581,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_578])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:28:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.36  
% 2.50/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.36  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.50/1.36  
% 2.50/1.36  %Foreground sorts:
% 2.50/1.36  
% 2.50/1.36  
% 2.50/1.36  %Background operators:
% 2.50/1.36  
% 2.50/1.36  
% 2.50/1.36  %Foreground operators:
% 2.50/1.36  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.36  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.50/1.36  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.36  
% 2.81/1.37  tff(f_77, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C))) => r1_tarski(B, k5_setfam_1(u1_struct_0(A), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_tops_2)).
% 2.81/1.37  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.81/1.37  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.81/1.37  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.81/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/1.37  tff(f_54, axiom, (![A, B, C]: (((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) => m1_subset_1(k1_tops_2(A, B, C), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_2)).
% 2.81/1.37  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C)), k5_setfam_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_2)).
% 2.81/1.37  tff(c_20, plain, (~r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.37  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.37  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.37  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.37  tff(c_282, plain, (![A_52, B_53]: (u1_struct_0(k1_pre_topc(A_52, B_53))=B_53 | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.37  tff(c_293, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_282])).
% 2.81/1.37  tff(c_298, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_293])).
% 2.81/1.37  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.37  tff(c_63, plain, (![A_31, B_32]: (m1_subset_1(k5_setfam_1(A_31, B_32), k1_zfmisc_1(A_31)) | ~m1_subset_1(B_32, k1_zfmisc_1(k1_zfmisc_1(A_31))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.37  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.37  tff(c_68, plain, (![A_33, B_34]: (r1_tarski(k5_setfam_1(A_33, B_34), A_33) | ~m1_subset_1(B_34, k1_zfmisc_1(k1_zfmisc_1(A_33))))), inference(resolution, [status(thm)], [c_63, c_10])).
% 2.81/1.37  tff(c_78, plain, (![A_33, A_5]: (r1_tarski(k5_setfam_1(A_33, A_5), A_33) | ~r1_tarski(A_5, k1_zfmisc_1(A_33)))), inference(resolution, [status(thm)], [c_12, c_68])).
% 2.81/1.37  tff(c_88, plain, (![A_37, B_38]: (u1_struct_0(k1_pre_topc(A_37, B_38))=B_38 | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.37  tff(c_99, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_88])).
% 2.81/1.37  tff(c_104, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_99])).
% 2.81/1.37  tff(c_22, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.37  tff(c_45, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.37  tff(c_54, plain, (k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3'))='#skF_2' | ~r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3')), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_45])).
% 2.81/1.37  tff(c_87, plain, (~r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 2.81/1.37  tff(c_105, plain, (~r1_tarski(k5_setfam_1('#skF_2', k1_tops_2('#skF_1', '#skF_2', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_87])).
% 2.81/1.37  tff(c_120, plain, (~r1_tarski(k1_tops_2('#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_78, c_105])).
% 2.81/1.37  tff(c_121, plain, (![A_39, B_40, C_41]: (m1_subset_1(k1_tops_2(A_39, B_40, C_41), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_39, B_40))))) | ~m1_subset_1(C_41, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39)))) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.37  tff(c_129, plain, (![C_41]: (m1_subset_1(k1_tops_2('#skF_1', '#skF_2', C_41), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(C_41, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_121])).
% 2.81/1.37  tff(c_241, plain, (![C_50]: (m1_subset_1(k1_tops_2('#skF_1', '#skF_2', C_50), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(C_50, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_129])).
% 2.81/1.37  tff(c_249, plain, (![C_51]: (r1_tarski(k1_tops_2('#skF_1', '#skF_2', C_51), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(C_51, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(resolution, [status(thm)], [c_241, c_10])).
% 2.81/1.37  tff(c_260, plain, (r1_tarski(k1_tops_2('#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_249])).
% 2.81/1.37  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_260])).
% 2.81/1.37  tff(c_267, plain, (k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 2.81/1.37  tff(c_299, plain, (k5_setfam_1('#skF_2', k1_tops_2('#skF_1', '#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_267])).
% 2.81/1.37  tff(c_489, plain, (![A_69, B_70, C_71]: (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_69, B_70)), k1_tops_2(A_69, B_70, C_71)), k5_setfam_1(u1_struct_0(A_69), C_71)) | ~m1_subset_1(C_71, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69)))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.37  tff(c_506, plain, (![C_71]: (r1_tarski(k5_setfam_1('#skF_2', k1_tops_2('#skF_1', '#skF_2', C_71)), k5_setfam_1(u1_struct_0('#skF_1'), C_71)) | ~m1_subset_1(C_71, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_298, c_489])).
% 2.81/1.37  tff(c_573, plain, (![C_78]: (r1_tarski(k5_setfam_1('#skF_2', k1_tops_2('#skF_1', '#skF_2', C_78)), k5_setfam_1(u1_struct_0('#skF_1'), C_78)) | ~m1_subset_1(C_78, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_506])).
% 2.81/1.37  tff(c_578, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_299, c_573])).
% 2.81/1.37  tff(c_581, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_578])).
% 2.81/1.37  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_581])).
% 2.81/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.37  
% 2.81/1.37  Inference rules
% 2.81/1.37  ----------------------
% 2.81/1.37  #Ref     : 0
% 2.81/1.37  #Sup     : 131
% 2.81/1.37  #Fact    : 0
% 2.81/1.37  #Define  : 0
% 2.81/1.37  #Split   : 9
% 2.81/1.37  #Chain   : 0
% 2.81/1.37  #Close   : 0
% 2.81/1.37  
% 2.81/1.37  Ordering : KBO
% 2.81/1.37  
% 2.81/1.37  Simplification rules
% 2.81/1.37  ----------------------
% 2.81/1.37  #Subsume      : 7
% 2.81/1.37  #Demod        : 68
% 2.81/1.37  #Tautology    : 31
% 2.81/1.37  #SimpNegUnit  : 2
% 2.81/1.37  #BackRed      : 4
% 2.81/1.37  
% 2.81/1.37  #Partial instantiations: 0
% 2.81/1.37  #Strategies tried      : 1
% 2.81/1.37  
% 2.81/1.37  Timing (in seconds)
% 2.81/1.37  ----------------------
% 2.81/1.38  Preprocessing        : 0.28
% 2.81/1.38  Parsing              : 0.16
% 2.81/1.38  CNF conversion       : 0.02
% 2.81/1.38  Main loop            : 0.33
% 2.81/1.38  Inferencing          : 0.12
% 2.81/1.38  Reduction            : 0.10
% 2.81/1.38  Demodulation         : 0.07
% 2.81/1.38  BG Simplification    : 0.02
% 2.81/1.38  Subsumption          : 0.07
% 2.81/1.38  Abstraction          : 0.02
% 2.81/1.38  MUC search           : 0.00
% 2.81/1.38  Cooper               : 0.00
% 2.81/1.38  Total                : 0.65
% 2.81/1.38  Index Insertion      : 0.00
% 2.81/1.38  Index Deletion       : 0.00
% 2.81/1.38  Index Matching       : 0.00
% 2.81/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
