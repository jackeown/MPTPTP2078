%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:54 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  85 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_18,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_93,plain,(
    ! [A_30,B_31,C_32] :
      ( k9_subset_1(A_30,B_31,C_32) = k3_xboole_0(B_31,C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [B_31] : k9_subset_1(u1_struct_0('#skF_1'),B_31,'#skF_2') = k3_xboole_0(B_31,'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_93])).

tff(c_164,plain,(
    ! [A_38,C_39,B_40] :
      ( k9_subset_1(A_38,C_39,B_40) = k9_subset_1(A_38,B_40,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_166,plain,(
    ! [B_40] : k9_subset_1(u1_struct_0('#skF_1'),B_40,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_40) ),
    inference(resolution,[status(thm)],[c_22,c_164])).

tff(c_168,plain,(
    ! [B_40] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_40) = k3_xboole_0(B_40,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_166])).

tff(c_20,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_227,plain,(
    ! [A_44,B_45] :
      ( k2_pre_topc(A_44,B_45) = B_45
      | ~ v4_pre_topc(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_230,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_227])).

tff(c_233,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_230])).

tff(c_438,plain,(
    ! [A_56,B_57] :
      ( k9_subset_1(u1_struct_0(A_56),k2_pre_topc(A_56,B_57),k2_pre_topc(A_56,k3_subset_1(u1_struct_0(A_56),B_57))) = k2_tops_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_447,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_438])).

tff(c_451,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_2,c_168,c_447])).

tff(c_59,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    ! [A_24,B_25] : r1_tarski(k3_xboole_0(A_24,B_25),A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_4])).

tff(c_476,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_68])).

tff(c_484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:58:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.40  
% 2.50/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.40  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.50/1.40  
% 2.50/1.40  %Foreground sorts:
% 2.50/1.40  
% 2.50/1.40  
% 2.50/1.40  %Background operators:
% 2.50/1.40  
% 2.50/1.40  
% 2.50/1.40  %Foreground operators:
% 2.50/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.50/1.40  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.50/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.50/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.40  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.50/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.50/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.50/1.40  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.50/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.40  
% 2.50/1.42  tff(f_71, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 2.50/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.50/1.42  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.50/1.42  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.50/1.42  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.50/1.42  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 2.50/1.42  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.50/1.42  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.50/1.42  tff(c_18, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.50/1.42  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.50/1.42  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.50/1.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.50/1.42  tff(c_93, plain, (![A_30, B_31, C_32]: (k9_subset_1(A_30, B_31, C_32)=k3_xboole_0(B_31, C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.50/1.42  tff(c_96, plain, (![B_31]: (k9_subset_1(u1_struct_0('#skF_1'), B_31, '#skF_2')=k3_xboole_0(B_31, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_93])).
% 2.50/1.42  tff(c_164, plain, (![A_38, C_39, B_40]: (k9_subset_1(A_38, C_39, B_40)=k9_subset_1(A_38, B_40, C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.50/1.42  tff(c_166, plain, (![B_40]: (k9_subset_1(u1_struct_0('#skF_1'), B_40, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_40))), inference(resolution, [status(thm)], [c_22, c_164])).
% 2.50/1.42  tff(c_168, plain, (![B_40]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_40)=k3_xboole_0(B_40, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_166])).
% 2.50/1.42  tff(c_20, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.50/1.42  tff(c_227, plain, (![A_44, B_45]: (k2_pre_topc(A_44, B_45)=B_45 | ~v4_pre_topc(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.50/1.42  tff(c_230, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_227])).
% 2.50/1.42  tff(c_233, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_230])).
% 2.50/1.42  tff(c_438, plain, (![A_56, B_57]: (k9_subset_1(u1_struct_0(A_56), k2_pre_topc(A_56, B_57), k2_pre_topc(A_56, k3_subset_1(u1_struct_0(A_56), B_57)))=k2_tops_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.50/1.42  tff(c_447, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_233, c_438])).
% 2.50/1.42  tff(c_451, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_2, c_168, c_447])).
% 2.50/1.42  tff(c_59, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.42  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.50/1.42  tff(c_68, plain, (![A_24, B_25]: (r1_tarski(k3_xboole_0(A_24, B_25), A_24))), inference(superposition, [status(thm), theory('equality')], [c_59, c_4])).
% 2.50/1.42  tff(c_476, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_451, c_68])).
% 2.50/1.42  tff(c_484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_476])).
% 2.50/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.42  
% 2.50/1.42  Inference rules
% 2.50/1.42  ----------------------
% 2.50/1.42  #Ref     : 0
% 2.50/1.42  #Sup     : 116
% 2.50/1.42  #Fact    : 0
% 2.50/1.42  #Define  : 0
% 2.50/1.42  #Split   : 0
% 2.50/1.42  #Chain   : 0
% 2.50/1.42  #Close   : 0
% 2.50/1.42  
% 2.50/1.42  Ordering : KBO
% 2.50/1.42  
% 2.50/1.42  Simplification rules
% 2.50/1.42  ----------------------
% 2.50/1.42  #Subsume      : 5
% 2.50/1.42  #Demod        : 67
% 2.50/1.42  #Tautology    : 67
% 2.50/1.42  #SimpNegUnit  : 1
% 2.50/1.42  #BackRed      : 0
% 2.50/1.42  
% 2.50/1.42  #Partial instantiations: 0
% 2.50/1.42  #Strategies tried      : 1
% 2.50/1.42  
% 2.50/1.42  Timing (in seconds)
% 2.50/1.42  ----------------------
% 2.50/1.42  Preprocessing        : 0.33
% 2.50/1.42  Parsing              : 0.17
% 2.50/1.42  CNF conversion       : 0.02
% 2.50/1.42  Main loop            : 0.30
% 2.50/1.42  Inferencing          : 0.10
% 2.50/1.42  Reduction            : 0.13
% 2.50/1.42  Demodulation         : 0.11
% 2.50/1.42  BG Simplification    : 0.02
% 2.50/1.42  Subsumption          : 0.04
% 2.50/1.42  Abstraction          : 0.02
% 2.50/1.42  MUC search           : 0.00
% 2.50/1.42  Cooper               : 0.00
% 2.50/1.42  Total                : 0.67
% 2.50/1.42  Index Insertion      : 0.00
% 2.50/1.42  Index Deletion       : 0.00
% 2.50/1.42  Index Matching       : 0.00
% 2.50/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
