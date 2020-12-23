%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:21 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   55 (  89 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 128 expanded)
%              Number of equality atoms :   12 (  32 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_45,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_20,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_39,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_54,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = k2_struct_0(A_25)
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_59,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_32,c_54])).

tff(c_63,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_59])).

tff(c_155,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k2_pre_topc(A_49,B_50),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_163,plain,(
    ! [B_50] :
      ( m1_subset_1(k2_pre_topc('#skF_3',B_50),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_155])).

tff(c_168,plain,(
    ! [B_51] :
      ( m1_subset_1(k2_pre_topc('#skF_3',B_51),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_163])).

tff(c_24,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [A_33,B_34] :
      ( r2_hidden(A_33,B_34)
      | v1_xboole_0(B_34)
      | ~ m1_subset_1(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,(
    ! [A_33,A_3] :
      ( r1_tarski(A_33,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_33,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_81,c_8])).

tff(c_88,plain,(
    ! [A_33,A_3] :
      ( r1_tarski(A_33,A_3)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(A_3)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_85])).

tff(c_176,plain,(
    ! [B_52] :
      ( r1_tarski(k2_pre_topc('#skF_3',B_52),k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_168,c_88])).

tff(c_36,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) != k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_95,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(B_37,k2_pre_topc(A_38,B_37))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_104,plain,(
    ! [A_39] :
      ( r1_tarski(u1_struct_0(A_39),k2_pre_topc(A_39,u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_39,c_95])).

tff(c_109,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_104])).

tff(c_115,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_pre_topc('#skF_3',k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_109])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_pre_topc('#skF_3',k2_struct_0('#skF_3')),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_122,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3',k2_struct_0('#skF_3')),k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_119])).

tff(c_179,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_176,c_122])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.22  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_1
% 1.98/1.22  
% 1.98/1.22  %Foreground sorts:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Background operators:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Foreground operators:
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.98/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.98/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.22  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.98/1.22  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.98/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.22  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 1.98/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.22  
% 2.08/1.24  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.08/1.24  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.08/1.24  tff(f_77, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 2.08/1.24  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.08/1.24  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.08/1.24  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.08/1.24  tff(f_45, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.08/1.24  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.08/1.24  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.08/1.24  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.08/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.08/1.24  tff(c_20, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.08/1.24  tff(c_22, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.08/1.24  tff(c_39, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.08/1.24  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.08/1.24  tff(c_32, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.08/1.24  tff(c_54, plain, (![A_25]: (u1_struct_0(A_25)=k2_struct_0(A_25) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.08/1.24  tff(c_59, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_32, c_54])).
% 2.08/1.24  tff(c_63, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_59])).
% 2.08/1.24  tff(c_155, plain, (![A_49, B_50]: (m1_subset_1(k2_pre_topc(A_49, B_50), k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.24  tff(c_163, plain, (![B_50]: (m1_subset_1(k2_pre_topc('#skF_3', B_50), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_155])).
% 2.08/1.24  tff(c_168, plain, (![B_51]: (m1_subset_1(k2_pre_topc('#skF_3', B_51), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_51, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_163])).
% 2.08/1.24  tff(c_24, plain, (![A_10]: (~v1_xboole_0(k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.08/1.24  tff(c_81, plain, (![A_33, B_34]: (r2_hidden(A_33, B_34) | v1_xboole_0(B_34) | ~m1_subset_1(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.24  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.08/1.24  tff(c_85, plain, (![A_33, A_3]: (r1_tarski(A_33, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_33, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_81, c_8])).
% 2.08/1.24  tff(c_88, plain, (![A_33, A_3]: (r1_tarski(A_33, A_3) | ~m1_subset_1(A_33, k1_zfmisc_1(A_3)))), inference(negUnitSimplification, [status(thm)], [c_24, c_85])).
% 2.08/1.24  tff(c_176, plain, (![B_52]: (r1_tarski(k2_pre_topc('#skF_3', B_52), k2_struct_0('#skF_3')) | ~m1_subset_1(B_52, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_168, c_88])).
% 2.08/1.24  tff(c_36, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.08/1.24  tff(c_95, plain, (![B_37, A_38]: (r1_tarski(B_37, k2_pre_topc(A_38, B_37)) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.08/1.24  tff(c_104, plain, (![A_39]: (r1_tarski(u1_struct_0(A_39), k2_pre_topc(A_39, u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_39, c_95])).
% 2.08/1.24  tff(c_109, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_63, c_104])).
% 2.08/1.24  tff(c_115, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_pre_topc('#skF_3', k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_109])).
% 2.08/1.24  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.24  tff(c_119, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~r1_tarski(k2_pre_topc('#skF_3', k2_struct_0('#skF_3')), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_115, c_2])).
% 2.08/1.24  tff(c_122, plain, (~r1_tarski(k2_pre_topc('#skF_3', k2_struct_0('#skF_3')), k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_36, c_119])).
% 2.08/1.24  tff(c_179, plain, (~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_176, c_122])).
% 2.08/1.24  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_179])).
% 2.08/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.24  
% 2.08/1.24  Inference rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Ref     : 0
% 2.08/1.24  #Sup     : 29
% 2.08/1.24  #Fact    : 0
% 2.08/1.24  #Define  : 0
% 2.08/1.24  #Split   : 0
% 2.08/1.24  #Chain   : 0
% 2.08/1.24  #Close   : 0
% 2.08/1.24  
% 2.08/1.24  Ordering : KBO
% 2.08/1.24  
% 2.08/1.24  Simplification rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Subsume      : 0
% 2.08/1.24  #Demod        : 14
% 2.08/1.24  #Tautology    : 10
% 2.08/1.24  #SimpNegUnit  : 2
% 2.08/1.24  #BackRed      : 0
% 2.08/1.24  
% 2.08/1.24  #Partial instantiations: 0
% 2.08/1.24  #Strategies tried      : 1
% 2.08/1.24  
% 2.08/1.24  Timing (in seconds)
% 2.08/1.24  ----------------------
% 2.08/1.24  Preprocessing        : 0.31
% 2.08/1.24  Parsing              : 0.17
% 2.08/1.24  CNF conversion       : 0.02
% 2.08/1.24  Main loop            : 0.16
% 2.08/1.24  Inferencing          : 0.06
% 2.08/1.24  Reduction            : 0.05
% 2.08/1.24  Demodulation         : 0.04
% 2.08/1.24  BG Simplification    : 0.01
% 2.08/1.24  Subsumption          : 0.03
% 2.08/1.24  Abstraction          : 0.01
% 2.08/1.24  MUC search           : 0.00
% 2.08/1.24  Cooper               : 0.00
% 2.08/1.24  Total                : 0.50
% 2.08/1.24  Index Insertion      : 0.00
% 2.08/1.24  Index Deletion       : 0.00
% 2.08/1.24  Index Matching       : 0.00
% 2.08/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
