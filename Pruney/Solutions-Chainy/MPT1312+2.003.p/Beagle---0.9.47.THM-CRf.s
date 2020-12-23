%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:57 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 (  98 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_38,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(k1_zfmisc_1(A_3),k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    ! [A_36,C_37,B_38] :
      ( m1_subset_1(A_36,C_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,(
    ! [A_41,B_42,A_43] :
      ( m1_subset_1(A_41,B_42)
      | ~ r2_hidden(A_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(resolution,[status(thm)],[c_16,c_62])).

tff(c_102,plain,(
    ! [A_47,B_48,B_49] :
      ( m1_subset_1(A_47,B_48)
      | ~ r1_tarski(B_49,B_48)
      | v1_xboole_0(B_49)
      | ~ m1_subset_1(A_47,B_49) ) ),
    inference(resolution,[status(thm)],[c_12,c_81])).

tff(c_106,plain,(
    ! [A_47,B_4,A_3] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_4))
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_47,k1_zfmisc_1(A_3))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_102])).

tff(c_118,plain,(
    ! [A_50,B_51,A_52] :
      ( m1_subset_1(A_50,k1_zfmisc_1(B_51))
      | ~ m1_subset_1(A_50,k1_zfmisc_1(A_52))
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_106])).

tff(c_136,plain,(
    ! [B_56] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(B_56))
      | ~ r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')),B_56) ) ),
    inference(resolution,[status(thm)],[c_24,c_118])).

tff(c_153,plain,(
    ! [B_57] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(B_57)))
      | ~ r1_tarski(u1_struct_0('#skF_2'),B_57) ) ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_22,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_167,plain,(
    ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_153,c_22])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_128,plain,(
    ! [C_53,A_54,B_55] :
      ( m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(B_55)))
      | ~ m1_pre_topc(B_55,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_332,plain,(
    ! [A_77,A_78,B_79] :
      ( m1_subset_1(A_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_pre_topc(B_79,A_78)
      | ~ l1_pre_topc(A_78)
      | ~ r1_tarski(A_77,u1_struct_0(B_79)) ) ),
    inference(resolution,[status(thm)],[c_16,c_128])).

tff(c_334,plain,(
    ! [A_77] :
      ( m1_subset_1(A_77,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_77,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_26,c_332])).

tff(c_338,plain,(
    ! [A_80] :
      ( m1_subset_1(A_80,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_80,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_334])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_352,plain,(
    ! [A_81] :
      ( r1_tarski(A_81,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_81,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_338,c_14])).

tff(c_359,plain,(
    r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_352])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:57:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.33  
% 2.43/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.43/1.33  
% 2.43/1.33  %Foreground sorts:
% 2.43/1.33  
% 2.43/1.33  
% 2.43/1.33  %Background operators:
% 2.43/1.33  
% 2.43/1.33  
% 2.43/1.33  %Foreground operators:
% 2.43/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.43/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.43/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.43/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.33  
% 2.43/1.35  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.43/1.35  tff(f_75, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 2.43/1.35  tff(f_38, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.43/1.35  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.43/1.35  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.43/1.35  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.43/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.43/1.35  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.43/1.35  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k1_zfmisc_1(A_3), k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.35  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.35  tff(c_10, plain, (![A_5]: (~v1_xboole_0(k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.43/1.35  tff(c_12, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.43/1.35  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.43/1.35  tff(c_62, plain, (![A_36, C_37, B_38]: (m1_subset_1(A_36, C_37) | ~m1_subset_1(B_38, k1_zfmisc_1(C_37)) | ~r2_hidden(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.43/1.35  tff(c_81, plain, (![A_41, B_42, A_43]: (m1_subset_1(A_41, B_42) | ~r2_hidden(A_41, A_43) | ~r1_tarski(A_43, B_42))), inference(resolution, [status(thm)], [c_16, c_62])).
% 2.43/1.35  tff(c_102, plain, (![A_47, B_48, B_49]: (m1_subset_1(A_47, B_48) | ~r1_tarski(B_49, B_48) | v1_xboole_0(B_49) | ~m1_subset_1(A_47, B_49))), inference(resolution, [status(thm)], [c_12, c_81])).
% 2.43/1.35  tff(c_106, plain, (![A_47, B_4, A_3]: (m1_subset_1(A_47, k1_zfmisc_1(B_4)) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_47, k1_zfmisc_1(A_3)) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_102])).
% 2.43/1.35  tff(c_118, plain, (![A_50, B_51, A_52]: (m1_subset_1(A_50, k1_zfmisc_1(B_51)) | ~m1_subset_1(A_50, k1_zfmisc_1(A_52)) | ~r1_tarski(A_52, B_51))), inference(negUnitSimplification, [status(thm)], [c_10, c_106])).
% 2.43/1.35  tff(c_136, plain, (![B_56]: (m1_subset_1('#skF_3', k1_zfmisc_1(B_56)) | ~r1_tarski(k1_zfmisc_1(u1_struct_0('#skF_2')), B_56))), inference(resolution, [status(thm)], [c_24, c_118])).
% 2.43/1.35  tff(c_153, plain, (![B_57]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(B_57))) | ~r1_tarski(u1_struct_0('#skF_2'), B_57))), inference(resolution, [status(thm)], [c_8, c_136])).
% 2.43/1.35  tff(c_22, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.35  tff(c_167, plain, (~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_153, c_22])).
% 2.43/1.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.35  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.35  tff(c_26, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.35  tff(c_128, plain, (![C_53, A_54, B_55]: (m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(B_55))) | ~m1_pre_topc(B_55, A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.43/1.35  tff(c_332, plain, (![A_77, A_78, B_79]: (m1_subset_1(A_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_pre_topc(B_79, A_78) | ~l1_pre_topc(A_78) | ~r1_tarski(A_77, u1_struct_0(B_79)))), inference(resolution, [status(thm)], [c_16, c_128])).
% 2.43/1.35  tff(c_334, plain, (![A_77]: (m1_subset_1(A_77, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_77, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_26, c_332])).
% 2.43/1.35  tff(c_338, plain, (![A_80]: (m1_subset_1(A_80, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_80, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_334])).
% 2.43/1.35  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.43/1.35  tff(c_352, plain, (![A_81]: (r1_tarski(A_81, u1_struct_0('#skF_1')) | ~r1_tarski(A_81, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_338, c_14])).
% 2.43/1.35  tff(c_359, plain, (r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_352])).
% 2.43/1.35  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_359])).
% 2.43/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.35  
% 2.43/1.35  Inference rules
% 2.43/1.35  ----------------------
% 2.43/1.35  #Ref     : 0
% 2.43/1.35  #Sup     : 75
% 2.43/1.35  #Fact    : 0
% 2.43/1.35  #Define  : 0
% 2.43/1.35  #Split   : 4
% 2.43/1.35  #Chain   : 0
% 2.43/1.35  #Close   : 0
% 2.43/1.35  
% 2.43/1.35  Ordering : KBO
% 2.43/1.35  
% 2.43/1.35  Simplification rules
% 2.43/1.35  ----------------------
% 2.43/1.35  #Subsume      : 13
% 2.43/1.35  #Demod        : 11
% 2.43/1.35  #Tautology    : 15
% 2.43/1.35  #SimpNegUnit  : 2
% 2.43/1.35  #BackRed      : 0
% 2.43/1.35  
% 2.43/1.35  #Partial instantiations: 0
% 2.43/1.35  #Strategies tried      : 1
% 2.43/1.35  
% 2.43/1.35  Timing (in seconds)
% 2.43/1.35  ----------------------
% 2.43/1.36  Preprocessing        : 0.29
% 2.43/1.36  Parsing              : 0.16
% 2.43/1.36  CNF conversion       : 0.02
% 2.43/1.36  Main loop            : 0.29
% 2.43/1.36  Inferencing          : 0.11
% 2.43/1.36  Reduction            : 0.08
% 2.43/1.36  Demodulation         : 0.05
% 2.43/1.36  BG Simplification    : 0.01
% 2.43/1.36  Subsumption          : 0.08
% 2.43/1.36  Abstraction          : 0.01
% 2.43/1.36  MUC search           : 0.00
% 2.43/1.36  Cooper               : 0.00
% 2.43/1.36  Total                : 0.63
% 2.43/1.36  Index Insertion      : 0.00
% 2.43/1.36  Index Deletion       : 0.00
% 2.43/1.36  Index Matching       : 0.00
% 2.43/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
