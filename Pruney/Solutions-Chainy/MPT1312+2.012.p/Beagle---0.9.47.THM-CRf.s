%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:58 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   51 (  59 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 104 expanded)
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

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_49,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_29,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_33,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_22,c_29])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [C_40,B_41,A_42] :
      ( r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [A_55,B_56,B_57] :
      ( r2_hidden('#skF_1'(A_55,B_56),B_57)
      | ~ r1_tarski(A_55,B_57)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_133,plain,(
    ! [A_58,B_59,B_60] :
      ( m1_subset_1('#skF_1'(A_58,B_59),B_60)
      | ~ r1_tarski(A_58,B_60)
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_120,c_10])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_147,plain,(
    ! [A_58,B_59,B_12] :
      ( r1_tarski('#skF_1'(A_58,B_59),B_12)
      | ~ r1_tarski(A_58,k1_zfmisc_1(B_12))
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_133,c_14])).

tff(c_8,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    ! [C_49,A_50,B_51] :
      ( m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(B_51)))
      | ~ m1_pre_topc(B_51,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_148,plain,(
    ! [A_61,A_62,B_63] :
      ( m1_subset_1(A_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_pre_topc(B_63,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ r1_tarski(A_61,u1_struct_0(B_63)) ) ),
    inference(resolution,[status(thm)],[c_16,c_100])).

tff(c_150,plain,(
    ! [A_61] :
      ( m1_subset_1(A_61,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_61,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_24,c_148])).

tff(c_154,plain,(
    ! [A_64] :
      ( m1_subset_1(A_64,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_64,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_150])).

tff(c_55,plain,(
    ! [A_36,B_37] :
      ( r2_hidden(A_36,B_37)
      | v1_xboole_0(B_37)
      | ~ m1_subset_1(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [A_1,B_37] :
      ( r1_tarski(A_1,B_37)
      | v1_xboole_0(B_37)
      | ~ m1_subset_1('#skF_1'(A_1,B_37),B_37) ) ),
    inference(resolution,[status(thm)],[c_55,c_4])).

tff(c_160,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski('#skF_1'(A_1,k1_zfmisc_1(u1_struct_0('#skF_2'))),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_154,c_63])).

tff(c_202,plain,(
    ! [A_71] :
      ( r1_tarski(A_71,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski('#skF_1'(A_71,k1_zfmisc_1(u1_struct_0('#skF_2'))),u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_160])).

tff(c_218,plain,(
    ! [A_72] :
      ( ~ r1_tarski(A_72,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_72,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_147,c_202])).

tff(c_34,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,k1_zfmisc_1(B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    ~ r1_tarski('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_34,c_20])).

tff(c_227,plain,(
    ~ r1_tarski('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_218,c_42])).

tff(c_233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.32  
% 2.17/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.17/1.32  
% 2.17/1.32  %Foreground sorts:
% 2.17/1.32  
% 2.17/1.32  
% 2.17/1.32  %Background operators:
% 2.17/1.32  
% 2.17/1.32  
% 2.17/1.32  %Foreground operators:
% 2.17/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.17/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.32  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.17/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.17/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.32  
% 2.17/1.34  tff(f_70, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 2.17/1.34  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.17/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.17/1.34  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.17/1.34  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.17/1.34  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.17/1.34  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.17/1.34  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.34  tff(c_29, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.34  tff(c_33, plain, (r1_tarski('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_22, c_29])).
% 2.17/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.34  tff(c_71, plain, (![C_40, B_41, A_42]: (r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.34  tff(c_120, plain, (![A_55, B_56, B_57]: (r2_hidden('#skF_1'(A_55, B_56), B_57) | ~r1_tarski(A_55, B_57) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_6, c_71])).
% 2.17/1.34  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.34  tff(c_133, plain, (![A_58, B_59, B_60]: (m1_subset_1('#skF_1'(A_58, B_59), B_60) | ~r1_tarski(A_58, B_60) | r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_120, c_10])).
% 2.17/1.34  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.34  tff(c_147, plain, (![A_58, B_59, B_12]: (r1_tarski('#skF_1'(A_58, B_59), B_12) | ~r1_tarski(A_58, k1_zfmisc_1(B_12)) | r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_133, c_14])).
% 2.17/1.34  tff(c_8, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.34  tff(c_26, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.34  tff(c_24, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.34  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.34  tff(c_100, plain, (![C_49, A_50, B_51]: (m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0(B_51))) | ~m1_pre_topc(B_51, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.17/1.34  tff(c_148, plain, (![A_61, A_62, B_63]: (m1_subset_1(A_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_pre_topc(B_63, A_62) | ~l1_pre_topc(A_62) | ~r1_tarski(A_61, u1_struct_0(B_63)))), inference(resolution, [status(thm)], [c_16, c_100])).
% 2.17/1.34  tff(c_150, plain, (![A_61]: (m1_subset_1(A_61, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_61, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_24, c_148])).
% 2.17/1.34  tff(c_154, plain, (![A_64]: (m1_subset_1(A_64, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_64, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_150])).
% 2.17/1.34  tff(c_55, plain, (![A_36, B_37]: (r2_hidden(A_36, B_37) | v1_xboole_0(B_37) | ~m1_subset_1(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.34  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.34  tff(c_63, plain, (![A_1, B_37]: (r1_tarski(A_1, B_37) | v1_xboole_0(B_37) | ~m1_subset_1('#skF_1'(A_1, B_37), B_37))), inference(resolution, [status(thm)], [c_55, c_4])).
% 2.17/1.34  tff(c_160, plain, (![A_1]: (r1_tarski(A_1, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski('#skF_1'(A_1, k1_zfmisc_1(u1_struct_0('#skF_2'))), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_154, c_63])).
% 2.17/1.34  tff(c_202, plain, (![A_71]: (r1_tarski(A_71, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski('#skF_1'(A_71, k1_zfmisc_1(u1_struct_0('#skF_2'))), u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_8, c_160])).
% 2.17/1.34  tff(c_218, plain, (![A_72]: (~r1_tarski(A_72, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_72, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_147, c_202])).
% 2.17/1.34  tff(c_34, plain, (![A_29, B_30]: (m1_subset_1(A_29, k1_zfmisc_1(B_30)) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.34  tff(c_20, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.34  tff(c_42, plain, (~r1_tarski('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_34, c_20])).
% 2.17/1.34  tff(c_227, plain, (~r1_tarski('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_218, c_42])).
% 2.17/1.34  tff(c_233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33, c_227])).
% 2.17/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.34  
% 2.17/1.34  Inference rules
% 2.17/1.34  ----------------------
% 2.17/1.34  #Ref     : 0
% 2.17/1.34  #Sup     : 41
% 2.17/1.34  #Fact    : 0
% 2.17/1.34  #Define  : 0
% 2.17/1.34  #Split   : 1
% 2.17/1.34  #Chain   : 0
% 2.17/1.34  #Close   : 0
% 2.17/1.34  
% 2.17/1.34  Ordering : KBO
% 2.17/1.34  
% 2.17/1.34  Simplification rules
% 2.17/1.34  ----------------------
% 2.17/1.34  #Subsume      : 1
% 2.17/1.34  #Demod        : 4
% 2.17/1.34  #Tautology    : 7
% 2.17/1.34  #SimpNegUnit  : 4
% 2.17/1.34  #BackRed      : 0
% 2.17/1.34  
% 2.17/1.34  #Partial instantiations: 0
% 2.17/1.34  #Strategies tried      : 1
% 2.17/1.34  
% 2.17/1.34  Timing (in seconds)
% 2.17/1.34  ----------------------
% 2.17/1.34  Preprocessing        : 0.30
% 2.17/1.34  Parsing              : 0.16
% 2.17/1.34  CNF conversion       : 0.02
% 2.17/1.34  Main loop            : 0.22
% 2.17/1.34  Inferencing          : 0.09
% 2.17/1.34  Reduction            : 0.05
% 2.17/1.34  Demodulation         : 0.04
% 2.17/1.34  BG Simplification    : 0.01
% 2.17/1.34  Subsumption          : 0.05
% 2.17/1.34  Abstraction          : 0.01
% 2.17/1.34  MUC search           : 0.00
% 2.17/1.34  Cooper               : 0.00
% 2.17/1.34  Total                : 0.55
% 2.17/1.34  Index Insertion      : 0.00
% 2.17/1.34  Index Deletion       : 0.00
% 2.17/1.34  Index Matching       : 0.00
% 2.17/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
