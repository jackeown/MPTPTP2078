%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:29 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   54 (  99 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 167 expanded)
%              Number of equality atoms :   16 (  51 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_14] :
      ( A_14 = '#skF_3'
      | ~ v1_xboole_0(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2])).

tff(c_52,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_48])).

tff(c_28,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_68,plain,(
    m1_setfam_1('#skF_1',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_12,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_12])).

tff(c_54,plain,(
    k3_tarski('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_35])).

tff(c_102,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,k3_tarski(B_22))
      | ~ m1_setfam_1(B_22,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    ! [A_21] :
      ( r1_tarski(A_21,'#skF_1')
      | ~ m1_setfam_1('#skF_1',A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_102])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_37,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_8])).

tff(c_77,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_37])).

tff(c_20,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_141,plain,(
    ! [C_31,B_32,A_33] :
      ( v1_xboole_0(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(B_32,A_33)))
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_161,plain,(
    ! [A_35,A_36,B_37] :
      ( v1_xboole_0(A_35)
      | ~ v1_xboole_0(A_36)
      | ~ r1_tarski(A_35,k2_zfmisc_1(B_37,A_36)) ) ),
    inference(resolution,[status(thm)],[c_20,c_141])).

tff(c_164,plain,(
    ! [A_35] :
      ( v1_xboole_0(A_35)
      | ~ v1_xboole_0('#skF_1')
      | ~ r1_tarski(A_35,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_161])).

tff(c_170,plain,(
    ! [A_38] :
      ( v1_xboole_0(A_38)
      | ~ r1_tarski(A_38,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_164])).

tff(c_175,plain,(
    ! [A_39] :
      ( v1_xboole_0(A_39)
      | ~ m1_setfam_1('#skF_1',A_39) ) ),
    inference(resolution,[status(thm)],[c_105,c_170])).

tff(c_179,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_175])).

tff(c_24,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_182,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_179,c_24])).

tff(c_188,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_182])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:55:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.34  
% 2.05/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.34  %$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.05/1.34  
% 2.05/1.34  %Foreground sorts:
% 2.05/1.34  
% 2.05/1.34  
% 2.05/1.34  %Background operators:
% 2.05/1.34  
% 2.05/1.34  
% 2.05/1.34  %Foreground operators:
% 2.05/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.05/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.34  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.05/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.05/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.05/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.05/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.34  
% 2.05/1.35  tff(f_75, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 2.05/1.35  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.05/1.35  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.05/1.35  tff(f_38, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.05/1.35  tff(f_42, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.05/1.35  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.05/1.35  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.05/1.35  tff(f_53, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.05/1.35  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.05/1.35  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.35  tff(c_32, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.35  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.35  tff(c_26, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.35  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.35  tff(c_48, plain, (![A_14]: (A_14='#skF_3' | ~v1_xboole_0(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2])).
% 2.05/1.35  tff(c_52, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_4, c_48])).
% 2.05/1.35  tff(c_28, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.35  tff(c_68, plain, (m1_setfam_1('#skF_1', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 2.05/1.35  tff(c_12, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.05/1.35  tff(c_35, plain, (k3_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_12])).
% 2.05/1.35  tff(c_54, plain, (k3_tarski('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_35])).
% 2.05/1.35  tff(c_102, plain, (![A_21, B_22]: (r1_tarski(A_21, k3_tarski(B_22)) | ~m1_setfam_1(B_22, A_21))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.05/1.35  tff(c_105, plain, (![A_21]: (r1_tarski(A_21, '#skF_1') | ~m1_setfam_1('#skF_1', A_21))), inference(superposition, [status(thm), theory('equality')], [c_54, c_102])).
% 2.05/1.35  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.35  tff(c_37, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_8])).
% 2.05/1.35  tff(c_77, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_37])).
% 2.05/1.35  tff(c_20, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.35  tff(c_141, plain, (![C_31, B_32, A_33]: (v1_xboole_0(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(B_32, A_33))) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.05/1.35  tff(c_161, plain, (![A_35, A_36, B_37]: (v1_xboole_0(A_35) | ~v1_xboole_0(A_36) | ~r1_tarski(A_35, k2_zfmisc_1(B_37, A_36)))), inference(resolution, [status(thm)], [c_20, c_141])).
% 2.05/1.35  tff(c_164, plain, (![A_35]: (v1_xboole_0(A_35) | ~v1_xboole_0('#skF_1') | ~r1_tarski(A_35, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_161])).
% 2.05/1.35  tff(c_170, plain, (![A_38]: (v1_xboole_0(A_38) | ~r1_tarski(A_38, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_164])).
% 2.05/1.35  tff(c_175, plain, (![A_39]: (v1_xboole_0(A_39) | ~m1_setfam_1('#skF_1', A_39))), inference(resolution, [status(thm)], [c_105, c_170])).
% 2.05/1.35  tff(c_179, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_175])).
% 2.05/1.35  tff(c_24, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.05/1.35  tff(c_182, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_179, c_24])).
% 2.05/1.35  tff(c_188, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_182])).
% 2.05/1.35  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_188])).
% 2.05/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.35  
% 2.05/1.35  Inference rules
% 2.05/1.35  ----------------------
% 2.05/1.35  #Ref     : 0
% 2.05/1.35  #Sup     : 36
% 2.05/1.35  #Fact    : 0
% 2.05/1.35  #Define  : 0
% 2.05/1.35  #Split   : 0
% 2.05/1.35  #Chain   : 0
% 2.05/1.35  #Close   : 0
% 2.05/1.35  
% 2.05/1.35  Ordering : KBO
% 2.05/1.35  
% 2.05/1.35  Simplification rules
% 2.05/1.35  ----------------------
% 2.05/1.35  #Subsume      : 1
% 2.05/1.35  #Demod        : 26
% 2.05/1.35  #Tautology    : 22
% 2.05/1.35  #SimpNegUnit  : 1
% 2.05/1.35  #BackRed      : 3
% 2.05/1.35  
% 2.05/1.35  #Partial instantiations: 0
% 2.05/1.35  #Strategies tried      : 1
% 2.05/1.35  
% 2.05/1.35  Timing (in seconds)
% 2.05/1.35  ----------------------
% 2.05/1.36  Preprocessing        : 0.36
% 2.05/1.36  Parsing              : 0.20
% 2.05/1.36  CNF conversion       : 0.02
% 2.05/1.36  Main loop            : 0.16
% 2.05/1.36  Inferencing          : 0.06
% 2.05/1.36  Reduction            : 0.06
% 2.05/1.36  Demodulation         : 0.04
% 2.05/1.36  BG Simplification    : 0.01
% 2.05/1.36  Subsumption          : 0.02
% 2.05/1.36  Abstraction          : 0.01
% 2.05/1.36  MUC search           : 0.00
% 2.05/1.36  Cooper               : 0.00
% 2.05/1.36  Total                : 0.55
% 2.05/1.36  Index Insertion      : 0.00
% 2.05/1.36  Index Deletion       : 0.00
% 2.05/1.36  Index Matching       : 0.00
% 2.05/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
