%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:55 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 143 expanded)
%              Number of leaves         :   25 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 251 expanded)
%              Number of equality atoms :   21 (  58 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(c_24,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_54,plain,(
    ! [A_28,B_29,C_30] :
      ( k9_subset_1(A_28,B_29,C_30) = k3_xboole_0(B_29,C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    ! [B_29] : k9_subset_1(u1_struct_0('#skF_1'),B_29,'#skF_2') = k3_xboole_0(B_29,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_54])).

tff(c_184,plain,(
    ! [A_56,C_57,B_58] :
      ( k9_subset_1(A_56,C_57,B_58) = k9_subset_1(A_56,B_58,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_196,plain,(
    ! [B_58] : k9_subset_1(u1_struct_0('#skF_1'),B_58,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_58) ),
    inference(resolution,[status(thm)],[c_28,c_184])).

tff(c_205,plain,(
    ! [B_59] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_59) = k3_xboole_0(B_59,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_196])).

tff(c_70,plain,(
    ! [B_32,B_33,A_34] :
      ( k9_subset_1(B_32,B_33,A_34) = k3_xboole_0(B_33,A_34)
      | ~ r1_tarski(A_34,B_32) ) ),
    inference(resolution,[status(thm)],[c_16,c_54])).

tff(c_77,plain,(
    ! [B_2,B_33] : k9_subset_1(B_2,B_33,B_2) = k3_xboole_0(B_33,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_222,plain,(
    k3_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_77])).

tff(c_87,plain,(
    ! [A_37,B_38,C_39] :
      ( m1_subset_1(k9_subset_1(A_37,B_38,C_39),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118,plain,(
    ! [A_42,B_43,C_44] :
      ( r1_tarski(k9_subset_1(A_42,B_43,C_44),A_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_42)) ) ),
    inference(resolution,[status(thm)],[c_87,c_14])).

tff(c_125,plain,(
    ! [B_33,B_2] :
      ( r1_tarski(k3_xboole_0(B_33,B_2),B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_118])).

tff(c_259,plain,
    ( r1_tarski(k3_xboole_0('#skF_2',u1_struct_0('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_125])).

tff(c_344,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_347,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_344])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_347])).

tff(c_353,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_204,plain,(
    ! [B_58] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_58) = k3_xboole_0(B_58,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_196])).

tff(c_26,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_354,plain,(
    ! [A_62,B_63] :
      ( k2_pre_topc(A_62,B_63) = B_63
      | ~ v4_pre_topc(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_378,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_354])).

tff(c_393,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_378])).

tff(c_714,plain,(
    ! [A_82,B_83] :
      ( k9_subset_1(u1_struct_0(A_82),k2_pre_topc(A_82,B_83),k2_pre_topc(A_82,k3_subset_1(u1_struct_0(A_82),B_83))) = k2_tops_1(A_82,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_729,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_714])).

tff(c_733,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_204,c_729])).

tff(c_783,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_125])).

tff(c_801,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_783])).

tff(c_803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_801])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.40  
% 2.74/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.40  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.74/1.40  
% 2.74/1.40  %Foreground sorts:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Background operators:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Foreground operators:
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.40  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.74/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.74/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.74/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.40  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.74/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.74/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.74/1.40  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.74/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.40  
% 2.74/1.41  tff(f_79, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 2.74/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.74/1.41  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.74/1.41  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.74/1.41  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.74/1.41  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.74/1.41  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.74/1.41  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 2.74/1.41  tff(c_24, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.41  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.41  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.41  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.41  tff(c_54, plain, (![A_28, B_29, C_30]: (k9_subset_1(A_28, B_29, C_30)=k3_xboole_0(B_29, C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.74/1.41  tff(c_60, plain, (![B_29]: (k9_subset_1(u1_struct_0('#skF_1'), B_29, '#skF_2')=k3_xboole_0(B_29, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_54])).
% 2.74/1.41  tff(c_184, plain, (![A_56, C_57, B_58]: (k9_subset_1(A_56, C_57, B_58)=k9_subset_1(A_56, B_58, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.74/1.41  tff(c_196, plain, (![B_58]: (k9_subset_1(u1_struct_0('#skF_1'), B_58, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_58))), inference(resolution, [status(thm)], [c_28, c_184])).
% 2.74/1.41  tff(c_205, plain, (![B_59]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_59)=k3_xboole_0(B_59, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_196])).
% 2.74/1.41  tff(c_70, plain, (![B_32, B_33, A_34]: (k9_subset_1(B_32, B_33, A_34)=k3_xboole_0(B_33, A_34) | ~r1_tarski(A_34, B_32))), inference(resolution, [status(thm)], [c_16, c_54])).
% 2.74/1.41  tff(c_77, plain, (![B_2, B_33]: (k9_subset_1(B_2, B_33, B_2)=k3_xboole_0(B_33, B_2))), inference(resolution, [status(thm)], [c_6, c_70])).
% 2.74/1.41  tff(c_222, plain, (k3_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_205, c_77])).
% 2.74/1.41  tff(c_87, plain, (![A_37, B_38, C_39]: (m1_subset_1(k9_subset_1(A_37, B_38, C_39), k1_zfmisc_1(A_37)) | ~m1_subset_1(C_39, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.41  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.41  tff(c_118, plain, (![A_42, B_43, C_44]: (r1_tarski(k9_subset_1(A_42, B_43, C_44), A_42) | ~m1_subset_1(C_44, k1_zfmisc_1(A_42)))), inference(resolution, [status(thm)], [c_87, c_14])).
% 2.74/1.41  tff(c_125, plain, (![B_33, B_2]: (r1_tarski(k3_xboole_0(B_33, B_2), B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_118])).
% 2.74/1.41  tff(c_259, plain, (r1_tarski(k3_xboole_0('#skF_2', u1_struct_0('#skF_1')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_125])).
% 2.74/1.41  tff(c_344, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_259])).
% 2.74/1.41  tff(c_347, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_344])).
% 2.74/1.41  tff(c_351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_347])).
% 2.74/1.41  tff(c_353, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_259])).
% 2.74/1.41  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.41  tff(c_204, plain, (![B_58]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_58)=k3_xboole_0(B_58, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_196])).
% 2.74/1.41  tff(c_26, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.41  tff(c_354, plain, (![A_62, B_63]: (k2_pre_topc(A_62, B_63)=B_63 | ~v4_pre_topc(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.74/1.41  tff(c_378, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_354])).
% 2.74/1.41  tff(c_393, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_378])).
% 2.74/1.41  tff(c_714, plain, (![A_82, B_83]: (k9_subset_1(u1_struct_0(A_82), k2_pre_topc(A_82, B_83), k2_pre_topc(A_82, k3_subset_1(u1_struct_0(A_82), B_83)))=k2_tops_1(A_82, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.74/1.41  tff(c_729, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_393, c_714])).
% 2.74/1.41  tff(c_733, plain, (k3_xboole_0(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_204, c_729])).
% 2.74/1.41  tff(c_783, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_733, c_125])).
% 2.74/1.41  tff(c_801, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_353, c_783])).
% 2.74/1.41  tff(c_803, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_801])).
% 2.74/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  Inference rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Ref     : 0
% 2.74/1.41  #Sup     : 201
% 2.74/1.41  #Fact    : 0
% 2.74/1.41  #Define  : 0
% 2.74/1.41  #Split   : 3
% 2.74/1.41  #Chain   : 0
% 2.74/1.41  #Close   : 0
% 2.74/1.41  
% 2.74/1.41  Ordering : KBO
% 2.74/1.41  
% 2.74/1.41  Simplification rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Subsume      : 5
% 2.74/1.41  #Demod        : 63
% 2.74/1.41  #Tautology    : 52
% 2.74/1.41  #SimpNegUnit  : 2
% 2.74/1.41  #BackRed      : 0
% 2.74/1.41  
% 2.74/1.41  #Partial instantiations: 0
% 2.74/1.41  #Strategies tried      : 1
% 2.74/1.41  
% 2.74/1.41  Timing (in seconds)
% 2.74/1.41  ----------------------
% 2.74/1.42  Preprocessing        : 0.29
% 2.74/1.42  Parsing              : 0.15
% 2.74/1.42  CNF conversion       : 0.02
% 2.74/1.42  Main loop            : 0.36
% 2.74/1.42  Inferencing          : 0.13
% 2.74/1.42  Reduction            : 0.12
% 2.74/1.42  Demodulation         : 0.09
% 2.74/1.42  BG Simplification    : 0.02
% 2.74/1.42  Subsumption          : 0.07
% 2.74/1.42  Abstraction          : 0.03
% 2.74/1.42  MUC search           : 0.00
% 2.74/1.42  Cooper               : 0.00
% 2.74/1.42  Total                : 0.69
% 2.74/1.42  Index Insertion      : 0.00
% 2.74/1.42  Index Deletion       : 0.00
% 2.74/1.42  Index Matching       : 0.00
% 2.74/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
