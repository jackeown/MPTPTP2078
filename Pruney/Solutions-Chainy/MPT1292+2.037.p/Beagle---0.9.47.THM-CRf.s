%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:34 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   54 (  80 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :   63 ( 127 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2])).

tff(c_26,plain,(
    m1_setfam_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [A_2] : m1_subset_1('#skF_2',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6])).

tff(c_70,plain,(
    ! [A_32,B_33] :
      ( k5_setfam_1(A_32,B_33) = k3_tarski(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,(
    ! [A_36] : k5_setfam_1(A_36,'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_33,c_70])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k5_setfam_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(k1_zfmisc_1(A_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_99,plain,(
    ! [A_36] :
      ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(A_36))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_8])).

tff(c_106,plain,(
    ! [A_37] : m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_99])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_119,plain,(
    ! [A_38] : r1_tarski(k3_tarski('#skF_2'),A_38) ),
    inference(resolution,[status(thm)],[c_106,c_12])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_35,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ r1_tarski(A_1,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_4])).

tff(c_124,plain,(
    k3_tarski('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_119,c_35])).

tff(c_80,plain,(
    ! [A_32] : k5_setfam_1(A_32,'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_33,c_70])).

tff(c_149,plain,(
    ! [A_32] : k5_setfam_1(A_32,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_80])).

tff(c_173,plain,(
    ! [A_43,B_44] :
      ( k5_setfam_1(A_43,B_44) = A_43
      | ~ m1_setfam_1(B_44,A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_185,plain,(
    ! [A_43] :
      ( k5_setfam_1(A_43,'#skF_2') = A_43
      | ~ m1_setfam_1('#skF_2',A_43) ) ),
    inference(resolution,[status(thm)],[c_33,c_173])).

tff(c_190,plain,(
    ! [A_45] :
      ( A_45 = '#skF_2'
      | ~ m1_setfam_1('#skF_2',A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_185])).

tff(c_198,plain,(
    u1_struct_0('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_190])).

tff(c_22,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_204,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_22])).

tff(c_208,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36,c_204])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:23:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.20  
% 2.08/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.08/1.20  
% 2.08/1.20  %Foreground sorts:
% 2.08/1.20  
% 2.08/1.20  
% 2.08/1.20  %Background operators:
% 2.08/1.20  
% 2.08/1.20  
% 2.08/1.20  %Foreground operators:
% 2.08/1.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.08/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.20  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.08/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.08/1.20  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.08/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.08/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.20  
% 2.18/1.21  tff(f_78, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 2.18/1.21  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.18/1.21  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.18/1.21  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.18/1.21  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.18/1.21  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.18/1.21  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.18/1.21  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.18/1.21  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.18/1.21  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.18/1.21  tff(c_30, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.18/1.21  tff(c_24, plain, (k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.18/1.21  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.18/1.21  tff(c_36, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2])).
% 2.18/1.21  tff(c_26, plain, (m1_setfam_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.18/1.21  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.21  tff(c_33, plain, (![A_2]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6])).
% 2.18/1.21  tff(c_70, plain, (![A_32, B_33]: (k5_setfam_1(A_32, B_33)=k3_tarski(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(A_32))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.21  tff(c_94, plain, (![A_36]: (k5_setfam_1(A_36, '#skF_2')=k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_33, c_70])).
% 2.18/1.21  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k5_setfam_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(k1_zfmisc_1(A_3))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.18/1.21  tff(c_99, plain, (![A_36]: (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(A_36)) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(superposition, [status(thm), theory('equality')], [c_94, c_8])).
% 2.18/1.21  tff(c_106, plain, (![A_37]: (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_99])).
% 2.18/1.21  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.21  tff(c_119, plain, (![A_38]: (r1_tarski(k3_tarski('#skF_2'), A_38))), inference(resolution, [status(thm)], [c_106, c_12])).
% 2.18/1.21  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.18/1.21  tff(c_35, plain, (![A_1]: (A_1='#skF_2' | ~r1_tarski(A_1, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_4])).
% 2.18/1.21  tff(c_124, plain, (k3_tarski('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_119, c_35])).
% 2.18/1.21  tff(c_80, plain, (![A_32]: (k5_setfam_1(A_32, '#skF_2')=k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_33, c_70])).
% 2.18/1.21  tff(c_149, plain, (![A_32]: (k5_setfam_1(A_32, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_80])).
% 2.18/1.21  tff(c_173, plain, (![A_43, B_44]: (k5_setfam_1(A_43, B_44)=A_43 | ~m1_setfam_1(B_44, A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_43))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.18/1.21  tff(c_185, plain, (![A_43]: (k5_setfam_1(A_43, '#skF_2')=A_43 | ~m1_setfam_1('#skF_2', A_43))), inference(resolution, [status(thm)], [c_33, c_173])).
% 2.18/1.21  tff(c_190, plain, (![A_45]: (A_45='#skF_2' | ~m1_setfam_1('#skF_2', A_45))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_185])).
% 2.18/1.21  tff(c_198, plain, (u1_struct_0('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_26, c_190])).
% 2.18/1.21  tff(c_22, plain, (![A_14]: (~v1_xboole_0(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.21  tff(c_204, plain, (~v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_198, c_22])).
% 2.18/1.21  tff(c_208, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_36, c_204])).
% 2.18/1.21  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_208])).
% 2.18/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.21  
% 2.18/1.21  Inference rules
% 2.18/1.21  ----------------------
% 2.18/1.21  #Ref     : 0
% 2.18/1.21  #Sup     : 36
% 2.18/1.21  #Fact    : 0
% 2.18/1.21  #Define  : 0
% 2.18/1.21  #Split   : 0
% 2.18/1.21  #Chain   : 0
% 2.18/1.21  #Close   : 0
% 2.18/1.21  
% 2.18/1.21  Ordering : KBO
% 2.18/1.21  
% 2.18/1.21  Simplification rules
% 2.18/1.21  ----------------------
% 2.18/1.21  #Subsume      : 1
% 2.18/1.21  #Demod        : 25
% 2.18/1.21  #Tautology    : 18
% 2.18/1.21  #SimpNegUnit  : 1
% 2.18/1.21  #BackRed      : 4
% 2.18/1.21  
% 2.18/1.21  #Partial instantiations: 0
% 2.18/1.21  #Strategies tried      : 1
% 2.18/1.21  
% 2.18/1.21  Timing (in seconds)
% 2.18/1.21  ----------------------
% 2.18/1.22  Preprocessing        : 0.29
% 2.18/1.22  Parsing              : 0.16
% 2.18/1.22  CNF conversion       : 0.02
% 2.18/1.22  Main loop            : 0.15
% 2.18/1.22  Inferencing          : 0.05
% 2.18/1.22  Reduction            : 0.05
% 2.18/1.22  Demodulation         : 0.04
% 2.18/1.22  BG Simplification    : 0.01
% 2.18/1.22  Subsumption          : 0.02
% 2.18/1.22  Abstraction          : 0.01
% 2.18/1.22  MUC search           : 0.00
% 2.18/1.22  Cooper               : 0.00
% 2.18/1.22  Total                : 0.47
% 2.18/1.22  Index Insertion      : 0.00
% 2.18/1.22  Index Deletion       : 0.00
% 2.18/1.22  Index Matching       : 0.00
% 2.18/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
