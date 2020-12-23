%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:58 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   50 (  59 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 104 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_22,c_28])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_63,plain,(
    ! [A_40,C_41,B_42] :
      ( m1_subset_1(A_40,C_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(C_41))
      | ~ r2_hidden(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    ! [A_48,B_49,A_50] :
      ( m1_subset_1(A_48,B_49)
      | ~ r2_hidden(A_48,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_14,c_63])).

tff(c_159,plain,(
    ! [A_66,B_67,B_68] :
      ( m1_subset_1('#skF_1'(A_66,B_67),B_68)
      | ~ r1_tarski(A_66,B_68)
      | r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_177,plain,(
    ! [A_66,B_67,B_10] :
      ( r1_tarski('#skF_1'(A_66,B_67),B_10)
      | ~ r1_tarski(A_66,k1_zfmisc_1(B_10))
      | r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_159,c_12])).

tff(c_8,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_70,plain,(
    ! [C_43,A_44,B_45] :
      ( m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(B_45)))
      | ~ m1_pre_topc(B_45,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_255,plain,(
    ! [A_75,A_76,B_77] :
      ( m1_subset_1(A_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc(B_77,A_76)
      | ~ l1_pre_topc(A_76)
      | ~ r1_tarski(A_75,u1_struct_0(B_77)) ) ),
    inference(resolution,[status(thm)],[c_14,c_70])).

tff(c_257,plain,(
    ! [A_75] :
      ( m1_subset_1(A_75,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_75,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_24,c_255])).

tff(c_261,plain,(
    ! [A_78] :
      ( m1_subset_1(A_78,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_78,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_257])).

tff(c_43,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_1,B_33] :
      ( r1_tarski(A_1,B_33)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1('#skF_1'(A_1,B_33),B_33) ) ),
    inference(resolution,[status(thm)],[c_43,c_4])).

tff(c_267,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski('#skF_1'(A_1,k1_zfmisc_1(u1_struct_0('#skF_2'))),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_261,c_48])).

tff(c_428,plain,(
    ! [A_101] :
      ( r1_tarski(A_101,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski('#skF_1'(A_101,k1_zfmisc_1(u1_struct_0('#skF_2'))),u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_267])).

tff(c_442,plain,(
    ! [A_102] :
      ( ~ r1_tarski(A_102,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_102,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_177,c_428])).

tff(c_33,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_41,plain,(
    ~ r1_tarski('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_33,c_20])).

tff(c_455,plain,(
    ~ r1_tarski('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_442,c_41])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_455])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.34  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.55/1.34  
% 2.55/1.34  %Foreground sorts:
% 2.55/1.34  
% 2.55/1.34  
% 2.55/1.34  %Background operators:
% 2.55/1.34  
% 2.55/1.34  
% 2.55/1.34  %Foreground operators:
% 2.55/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.55/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.34  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.55/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.55/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.55/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.34  
% 2.55/1.36  tff(f_72, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 2.55/1.36  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.55/1.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.55/1.36  tff(f_51, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.55/1.36  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.55/1.36  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.55/1.36  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.55/1.36  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.36  tff(c_28, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.36  tff(c_32, plain, (r1_tarski('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_22, c_28])).
% 2.55/1.36  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.36  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.36  tff(c_63, plain, (![A_40, C_41, B_42]: (m1_subset_1(A_40, C_41) | ~m1_subset_1(B_42, k1_zfmisc_1(C_41)) | ~r2_hidden(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.55/1.36  tff(c_87, plain, (![A_48, B_49, A_50]: (m1_subset_1(A_48, B_49) | ~r2_hidden(A_48, A_50) | ~r1_tarski(A_50, B_49))), inference(resolution, [status(thm)], [c_14, c_63])).
% 2.55/1.36  tff(c_159, plain, (![A_66, B_67, B_68]: (m1_subset_1('#skF_1'(A_66, B_67), B_68) | ~r1_tarski(A_66, B_68) | r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_6, c_87])).
% 2.55/1.36  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.36  tff(c_177, plain, (![A_66, B_67, B_10]: (r1_tarski('#skF_1'(A_66, B_67), B_10) | ~r1_tarski(A_66, k1_zfmisc_1(B_10)) | r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_159, c_12])).
% 2.55/1.36  tff(c_8, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.55/1.36  tff(c_26, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.36  tff(c_24, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.36  tff(c_70, plain, (![C_43, A_44, B_45]: (m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(B_45))) | ~m1_pre_topc(B_45, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.55/1.36  tff(c_255, plain, (![A_75, A_76, B_77]: (m1_subset_1(A_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_pre_topc(B_77, A_76) | ~l1_pre_topc(A_76) | ~r1_tarski(A_75, u1_struct_0(B_77)))), inference(resolution, [status(thm)], [c_14, c_70])).
% 2.55/1.36  tff(c_257, plain, (![A_75]: (m1_subset_1(A_75, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_75, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_24, c_255])).
% 2.55/1.36  tff(c_261, plain, (![A_78]: (m1_subset_1(A_78, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_78, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_257])).
% 2.55/1.36  tff(c_43, plain, (![A_32, B_33]: (r2_hidden(A_32, B_33) | v1_xboole_0(B_33) | ~m1_subset_1(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.55/1.36  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.36  tff(c_48, plain, (![A_1, B_33]: (r1_tarski(A_1, B_33) | v1_xboole_0(B_33) | ~m1_subset_1('#skF_1'(A_1, B_33), B_33))), inference(resolution, [status(thm)], [c_43, c_4])).
% 2.55/1.36  tff(c_267, plain, (![A_1]: (r1_tarski(A_1, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski('#skF_1'(A_1, k1_zfmisc_1(u1_struct_0('#skF_2'))), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_261, c_48])).
% 2.55/1.36  tff(c_428, plain, (![A_101]: (r1_tarski(A_101, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski('#skF_1'(A_101, k1_zfmisc_1(u1_struct_0('#skF_2'))), u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_8, c_267])).
% 2.55/1.36  tff(c_442, plain, (![A_102]: (~r1_tarski(A_102, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_102, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_177, c_428])).
% 2.55/1.36  tff(c_33, plain, (![A_28, B_29]: (m1_subset_1(A_28, k1_zfmisc_1(B_29)) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.36  tff(c_20, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.36  tff(c_41, plain, (~r1_tarski('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_33, c_20])).
% 2.55/1.36  tff(c_455, plain, (~r1_tarski('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_442, c_41])).
% 2.55/1.36  tff(c_463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_455])).
% 2.55/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.36  
% 2.55/1.36  Inference rules
% 2.55/1.36  ----------------------
% 2.55/1.36  #Ref     : 0
% 2.55/1.36  #Sup     : 100
% 2.55/1.36  #Fact    : 0
% 2.55/1.36  #Define  : 0
% 2.55/1.36  #Split   : 3
% 2.55/1.36  #Chain   : 0
% 2.55/1.36  #Close   : 0
% 2.55/1.36  
% 2.55/1.36  Ordering : KBO
% 2.55/1.36  
% 2.55/1.36  Simplification rules
% 2.55/1.36  ----------------------
% 2.55/1.36  #Subsume      : 10
% 2.55/1.36  #Demod        : 9
% 2.55/1.36  #Tautology    : 12
% 2.55/1.36  #SimpNegUnit  : 14
% 2.55/1.36  #BackRed      : 0
% 2.55/1.36  
% 2.55/1.36  #Partial instantiations: 0
% 2.55/1.36  #Strategies tried      : 1
% 2.55/1.36  
% 2.55/1.36  Timing (in seconds)
% 2.55/1.36  ----------------------
% 2.55/1.36  Preprocessing        : 0.27
% 2.55/1.36  Parsing              : 0.16
% 2.55/1.36  CNF conversion       : 0.02
% 2.55/1.36  Main loop            : 0.30
% 2.55/1.36  Inferencing          : 0.12
% 2.55/1.36  Reduction            : 0.08
% 2.55/1.36  Demodulation         : 0.05
% 2.55/1.36  BG Simplification    : 0.01
% 2.55/1.36  Subsumption          : 0.07
% 2.55/1.36  Abstraction          : 0.01
% 2.55/1.36  MUC search           : 0.00
% 2.55/1.36  Cooper               : 0.00
% 2.55/1.36  Total                : 0.61
% 2.55/1.36  Index Insertion      : 0.00
% 2.55/1.36  Index Deletion       : 0.00
% 2.55/1.36  Index Matching       : 0.00
% 2.55/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
