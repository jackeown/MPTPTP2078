%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:24 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   50 (  57 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 117 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_yellow19,type,(
    k1_yellow19: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

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

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r2_waybel_7(A,k1_yellow19(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow19)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k1_yellow19(A,B))
        & v1_subset_1(k1_yellow19(A,B),u1_struct_0(k3_yellow_1(k2_struct_0(A))))
        & v2_waybel_0(k1_yellow19(A,B),k3_yellow_1(k2_struct_0(A)))
        & v13_waybel_0(k1_yellow19(A,B),k3_yellow_1(k2_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow19)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_yellow19(A,B),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow19)).

tff(f_31,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( v13_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
             => ( r2_waybel_7(A,C,B)
              <=> r1_tarski(k1_yellow19(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow19)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( v13_waybel_0(k1_yellow19(A_9,B_10),k3_yellow_1(k2_struct_0(A_9)))
      | ~ m1_subset_1(B_10,u1_struct_0(A_9))
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k1_yellow19(A_7,B_8),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_7)))))
      | ~ m1_subset_1(B_8,u1_struct_0(A_7))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1] : ~ v1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [B_28,A_29] :
      ( v1_subset_1(B_28,A_29)
      | B_28 = A_29
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_63,plain,(
    ! [A_1] :
      ( v1_subset_1('#skF_1'(A_1),A_1)
      | '#skF_1'(A_1) = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_57])).

tff(c_67,plain,(
    ! [A_1] : '#skF_1'(A_1) = A_1 ),
    inference(negUnitSimplification,[status(thm)],[c_2,c_63])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [A_1] : r1_tarski('#skF_1'(A_1),A_1) ),
    inference(resolution,[status(thm)],[c_4,c_40])).

tff(c_68,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_44])).

tff(c_147,plain,(
    ! [A_54,C_55,B_56] :
      ( r2_waybel_7(A_54,C_55,B_56)
      | ~ r1_tarski(k1_yellow19(A_54,B_56),C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_54)))))
      | ~ v13_waybel_0(C_55,k3_yellow_1(k2_struct_0(A_54)))
      | ~ m1_subset_1(B_56,u1_struct_0(A_54))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_157,plain,(
    ! [A_57,B_58] :
      ( r2_waybel_7(A_57,k1_yellow19(A_57,B_58),B_58)
      | ~ m1_subset_1(k1_yellow19(A_57,B_58),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_57)))))
      | ~ v13_waybel_0(k1_yellow19(A_57,B_58),k3_yellow_1(k2_struct_0(A_57)))
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_68,c_147])).

tff(c_165,plain,(
    ! [A_59,B_60] :
      ( r2_waybel_7(A_59,k1_yellow19(A_59,B_60),B_60)
      | ~ v13_waybel_0(k1_yellow19(A_59,B_60),k3_yellow_1(k2_struct_0(A_59)))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_14,c_157])).

tff(c_169,plain,(
    ! [A_61,B_62] :
      ( r2_waybel_7(A_61,k1_yellow19(A_61,B_62),B_62)
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_16,c_165])).

tff(c_28,plain,(
    ~ r2_waybel_7('#skF_2',k1_yellow19('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_172,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_169,c_28])).

tff(c_175,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_172])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.23  
% 2.09/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.23  %$ r2_waybel_7 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.09/1.23  
% 2.09/1.23  %Foreground sorts:
% 2.09/1.23  
% 2.09/1.23  
% 2.09/1.23  %Background operators:
% 2.09/1.23  
% 2.09/1.23  
% 2.09/1.23  %Foreground operators:
% 2.09/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.09/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.23  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.09/1.23  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.09/1.23  tff(k1_yellow19, type, k1_yellow19: ($i * $i) > $i).
% 2.09/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.09/1.23  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.09/1.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.09/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.23  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 2.09/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.23  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.09/1.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.09/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.09/1.23  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.09/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.23  
% 2.09/1.24  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_waybel_7(A, k1_yellow19(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_yellow19)).
% 2.09/1.24  tff(f_71, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (((~v1_xboole_0(k1_yellow19(A, B)) & v1_subset_1(k1_yellow19(A, B), u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(k1_yellow19(A, B), k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(k1_yellow19(A, B), k3_yellow_1(k2_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_yellow19)).
% 2.09/1.24  tff(f_53, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_yellow19(A, B), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow19)).
% 2.09/1.24  tff(f_31, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.09/1.24  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.09/1.24  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.09/1.24  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((v13_waybel_0(C, k3_yellow_1(k2_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (r2_waybel_7(A, C, B) <=> r1_tarski(k1_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow19)).
% 2.09/1.24  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.09/1.24  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.09/1.24  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.09/1.24  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.09/1.24  tff(c_16, plain, (![A_9, B_10]: (v13_waybel_0(k1_yellow19(A_9, B_10), k3_yellow_1(k2_struct_0(A_9))) | ~m1_subset_1(B_10, u1_struct_0(A_9)) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.09/1.24  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(k1_yellow19(A_7, B_8), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_7))))) | ~m1_subset_1(B_8, u1_struct_0(A_7)) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.24  tff(c_2, plain, (![A_1]: (~v1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.24  tff(c_4, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.24  tff(c_57, plain, (![B_28, A_29]: (v1_subset_1(B_28, A_29) | B_28=A_29 | ~m1_subset_1(B_28, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.09/1.24  tff(c_63, plain, (![A_1]: (v1_subset_1('#skF_1'(A_1), A_1) | '#skF_1'(A_1)=A_1)), inference(resolution, [status(thm)], [c_4, c_57])).
% 2.09/1.24  tff(c_67, plain, (![A_1]: ('#skF_1'(A_1)=A_1)), inference(negUnitSimplification, [status(thm)], [c_2, c_63])).
% 2.09/1.24  tff(c_40, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.24  tff(c_44, plain, (![A_1]: (r1_tarski('#skF_1'(A_1), A_1))), inference(resolution, [status(thm)], [c_4, c_40])).
% 2.09/1.24  tff(c_68, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_44])).
% 2.09/1.24  tff(c_147, plain, (![A_54, C_55, B_56]: (r2_waybel_7(A_54, C_55, B_56) | ~r1_tarski(k1_yellow19(A_54, B_56), C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_54))))) | ~v13_waybel_0(C_55, k3_yellow_1(k2_struct_0(A_54))) | ~m1_subset_1(B_56, u1_struct_0(A_54)) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.09/1.24  tff(c_157, plain, (![A_57, B_58]: (r2_waybel_7(A_57, k1_yellow19(A_57, B_58), B_58) | ~m1_subset_1(k1_yellow19(A_57, B_58), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_57))))) | ~v13_waybel_0(k1_yellow19(A_57, B_58), k3_yellow_1(k2_struct_0(A_57))) | ~m1_subset_1(B_58, u1_struct_0(A_57)) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(resolution, [status(thm)], [c_68, c_147])).
% 2.09/1.24  tff(c_165, plain, (![A_59, B_60]: (r2_waybel_7(A_59, k1_yellow19(A_59, B_60), B_60) | ~v13_waybel_0(k1_yellow19(A_59, B_60), k3_yellow_1(k2_struct_0(A_59))) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(resolution, [status(thm)], [c_14, c_157])).
% 2.09/1.24  tff(c_169, plain, (![A_61, B_62]: (r2_waybel_7(A_61, k1_yellow19(A_61, B_62), B_62) | ~m1_subset_1(B_62, u1_struct_0(A_61)) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(resolution, [status(thm)], [c_16, c_165])).
% 2.09/1.24  tff(c_28, plain, (~r2_waybel_7('#skF_2', k1_yellow19('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.09/1.24  tff(c_172, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_169, c_28])).
% 2.09/1.24  tff(c_175, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_172])).
% 2.09/1.24  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_175])).
% 2.09/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.24  
% 2.09/1.24  Inference rules
% 2.09/1.24  ----------------------
% 2.09/1.24  #Ref     : 0
% 2.09/1.24  #Sup     : 24
% 2.09/1.24  #Fact    : 0
% 2.09/1.24  #Define  : 0
% 2.09/1.24  #Split   : 0
% 2.09/1.24  #Chain   : 0
% 2.09/1.24  #Close   : 0
% 2.09/1.24  
% 2.09/1.24  Ordering : KBO
% 2.09/1.24  
% 2.09/1.24  Simplification rules
% 2.09/1.24  ----------------------
% 2.09/1.24  #Subsume      : 6
% 2.09/1.24  #Demod        : 12
% 2.09/1.24  #Tautology    : 6
% 2.09/1.24  #SimpNegUnit  : 4
% 2.09/1.24  #BackRed      : 4
% 2.09/1.24  
% 2.09/1.24  #Partial instantiations: 0
% 2.09/1.24  #Strategies tried      : 1
% 2.09/1.24  
% 2.09/1.24  Timing (in seconds)
% 2.09/1.24  ----------------------
% 2.09/1.24  Preprocessing        : 0.29
% 2.09/1.24  Parsing              : 0.16
% 2.09/1.25  CNF conversion       : 0.02
% 2.09/1.25  Main loop            : 0.18
% 2.09/1.25  Inferencing          : 0.08
% 2.09/1.25  Reduction            : 0.05
% 2.09/1.25  Demodulation         : 0.03
% 2.09/1.25  BG Simplification    : 0.01
% 2.09/1.25  Subsumption          : 0.03
% 2.09/1.25  Abstraction          : 0.01
% 2.09/1.25  MUC search           : 0.00
% 2.09/1.25  Cooper               : 0.00
% 2.09/1.25  Total                : 0.50
% 2.09/1.25  Index Insertion      : 0.00
% 2.09/1.25  Index Deletion       : 0.00
% 2.09/1.25  Index Matching       : 0.00
% 2.09/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
