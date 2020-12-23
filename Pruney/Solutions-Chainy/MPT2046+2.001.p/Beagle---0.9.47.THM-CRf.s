%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:24 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   77 (  97 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r2_waybel_7(A,k1_yellow19(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow19)).

tff(f_60,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_yellow19(A,B),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow19)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
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

tff(c_30,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( v13_waybel_0(k1_yellow19(A_5,B_6),k3_yellow_1(k2_struct_0(A_5)))
      | ~ m1_subset_1(B_6,u1_struct_0(A_5))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k1_yellow19(A_3,B_4),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_3)))))
      | ~ m1_subset_1(B_4,u1_struct_0(A_3))
      | ~ l1_pre_topc(A_3)
      | ~ v2_pre_topc(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_31,C_32,B_33] :
      ( r2_waybel_7(A_31,C_32,B_33)
      | ~ r1_tarski(k1_yellow19(A_31,B_33),C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_31)))))
      | ~ v13_waybel_0(C_32,k3_yellow_1(k2_struct_0(A_31)))
      | ~ m1_subset_1(B_33,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_61,plain,(
    ! [A_34,B_35] :
      ( r2_waybel_7(A_34,k1_yellow19(A_34,B_35),B_35)
      | ~ m1_subset_1(k1_yellow19(A_34,B_35),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_34)))))
      | ~ v13_waybel_0(k1_yellow19(A_34,B_35),k3_yellow_1(k2_struct_0(A_34)))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_65,plain,(
    ! [A_36,B_37] :
      ( r2_waybel_7(A_36,k1_yellow19(A_36,B_37),B_37)
      | ~ v13_waybel_0(k1_yellow19(A_36,B_37),k3_yellow_1(k2_struct_0(A_36)))
      | ~ m1_subset_1(B_37,u1_struct_0(A_36))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_8,c_61])).

tff(c_69,plain,(
    ! [A_38,B_39] :
      ( r2_waybel_7(A_38,k1_yellow19(A_38,B_39),B_39)
      | ~ m1_subset_1(B_39,u1_struct_0(A_38))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_10,c_65])).

tff(c_22,plain,(
    ~ r2_waybel_7('#skF_1',k1_yellow19('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_72,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_22])).

tff(c_75,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_72])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.21  %$ r2_waybel_7 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.98/1.21  
% 1.98/1.21  %Foreground sorts:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Background operators:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Foreground operators:
% 1.98/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.21  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.98/1.21  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.98/1.21  tff(k1_yellow19, type, k1_yellow19: ($i * $i) > $i).
% 1.98/1.21  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 1.98/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.98/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.21  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.21  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 1.98/1.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.98/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.21  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.98/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.21  
% 1.98/1.23  tff(f_92, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_waybel_7(A, k1_yellow19(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_yellow19)).
% 1.98/1.23  tff(f_60, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (((~v1_xboole_0(k1_yellow19(A, B)) & v1_subset_1(k1_yellow19(A, B), u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(k1_yellow19(A, B), k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(k1_yellow19(A, B), k3_yellow_1(k2_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_yellow19)).
% 1.98/1.23  tff(f_42, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_yellow19(A, B), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow19)).
% 1.98/1.23  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.98/1.23  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((v13_waybel_0(C, k3_yellow_1(k2_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (r2_waybel_7(A, C, B) <=> r1_tarski(k1_yellow19(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow19)).
% 1.98/1.23  tff(c_30, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.23  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.23  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.23  tff(c_24, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.23  tff(c_10, plain, (![A_5, B_6]: (v13_waybel_0(k1_yellow19(A_5, B_6), k3_yellow_1(k2_struct_0(A_5))) | ~m1_subset_1(B_6, u1_struct_0(A_5)) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.98/1.23  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k1_yellow19(A_3, B_4), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_3))))) | ~m1_subset_1(B_4, u1_struct_0(A_3)) | ~l1_pre_topc(A_3) | ~v2_pre_topc(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.98/1.23  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.23  tff(c_56, plain, (![A_31, C_32, B_33]: (r2_waybel_7(A_31, C_32, B_33) | ~r1_tarski(k1_yellow19(A_31, B_33), C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_31))))) | ~v13_waybel_0(C_32, k3_yellow_1(k2_struct_0(A_31))) | ~m1_subset_1(B_33, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.98/1.23  tff(c_61, plain, (![A_34, B_35]: (r2_waybel_7(A_34, k1_yellow19(A_34, B_35), B_35) | ~m1_subset_1(k1_yellow19(A_34, B_35), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_34))))) | ~v13_waybel_0(k1_yellow19(A_34, B_35), k3_yellow_1(k2_struct_0(A_34))) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(resolution, [status(thm)], [c_6, c_56])).
% 1.98/1.23  tff(c_65, plain, (![A_36, B_37]: (r2_waybel_7(A_36, k1_yellow19(A_36, B_37), B_37) | ~v13_waybel_0(k1_yellow19(A_36, B_37), k3_yellow_1(k2_struct_0(A_36))) | ~m1_subset_1(B_37, u1_struct_0(A_36)) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(resolution, [status(thm)], [c_8, c_61])).
% 1.98/1.23  tff(c_69, plain, (![A_38, B_39]: (r2_waybel_7(A_38, k1_yellow19(A_38, B_39), B_39) | ~m1_subset_1(B_39, u1_struct_0(A_38)) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(resolution, [status(thm)], [c_10, c_65])).
% 1.98/1.23  tff(c_22, plain, (~r2_waybel_7('#skF_1', k1_yellow19('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.98/1.23  tff(c_72, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_69, c_22])).
% 1.98/1.23  tff(c_75, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_72])).
% 1.98/1.23  tff(c_77, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_75])).
% 1.98/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  Inference rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Ref     : 0
% 1.98/1.23  #Sup     : 7
% 1.98/1.23  #Fact    : 0
% 1.98/1.23  #Define  : 0
% 1.98/1.23  #Split   : 0
% 1.98/1.23  #Chain   : 0
% 1.98/1.23  #Close   : 0
% 1.98/1.23  
% 1.98/1.23  Ordering : KBO
% 1.98/1.23  
% 1.98/1.23  Simplification rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Subsume      : 2
% 1.98/1.23  #Demod        : 7
% 1.98/1.23  #Tautology    : 2
% 1.98/1.23  #SimpNegUnit  : 2
% 1.98/1.23  #BackRed      : 0
% 1.98/1.23  
% 1.98/1.23  #Partial instantiations: 0
% 1.98/1.23  #Strategies tried      : 1
% 1.98/1.23  
% 1.98/1.23  Timing (in seconds)
% 1.98/1.23  ----------------------
% 1.98/1.23  Preprocessing        : 0.28
% 1.98/1.23  Parsing              : 0.15
% 1.98/1.23  CNF conversion       : 0.02
% 1.98/1.23  Main loop            : 0.14
% 1.98/1.23  Inferencing          : 0.06
% 1.98/1.23  Reduction            : 0.04
% 1.98/1.23  Demodulation         : 0.03
% 1.98/1.23  BG Simplification    : 0.01
% 1.98/1.23  Subsumption          : 0.03
% 1.98/1.23  Abstraction          : 0.01
% 1.98/1.23  MUC search           : 0.00
% 1.98/1.23  Cooper               : 0.00
% 1.98/1.23  Total                : 0.45
% 1.98/1.23  Index Insertion      : 0.00
% 1.98/1.23  Index Deletion       : 0.00
% 1.98/1.23  Index Matching       : 0.00
% 1.98/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
