%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:31 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   56 (  81 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :   67 ( 126 expanded)
%              Number of equality atoms :   15 (  31 expanded)
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

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_43,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2])).

tff(c_32,plain,(
    m1_setfam_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_39,plain,(
    ! [A_4] : m1_subset_1('#skF_2',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_86,plain,(
    ! [A_29,B_30] :
      ( k5_setfam_1(A_29,B_30) = k3_tarski(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    ! [A_29] : k5_setfam_1(A_29,'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_39,c_86])).

tff(c_125,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k5_setfam_1(A_42,B_43),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_137,plain,(
    ! [A_29] :
      ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(A_29))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_125])).

tff(c_143,plain,(
    ! [A_44] : m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(A_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_137])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_156,plain,(
    ! [A_45] : r1_tarski(k3_tarski('#skF_2'),A_45) ),
    inference(resolution,[status(thm)],[c_143,c_18])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_41,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10])).

tff(c_63,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'
      | ~ r1_tarski(A_3,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_41,c_63])).

tff(c_168,plain,(
    k3_tarski('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_156,c_72])).

tff(c_172,plain,(
    ! [A_29] : k5_setfam_1(A_29,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_96])).

tff(c_203,plain,(
    ! [A_48,B_49] :
      ( k5_setfam_1(A_48,B_49) = A_48
      | ~ m1_setfam_1(B_49,A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_215,plain,(
    ! [A_48] :
      ( k5_setfam_1(A_48,'#skF_2') = A_48
      | ~ m1_setfam_1('#skF_2',A_48) ) ),
    inference(resolution,[status(thm)],[c_39,c_203])).

tff(c_220,plain,(
    ! [A_50] :
      ( A_50 = '#skF_2'
      | ~ m1_setfam_1('#skF_2',A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_215])).

tff(c_224,plain,(
    u1_struct_0('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_220])).

tff(c_28,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_229,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_28])).

tff(c_233,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_43,c_229])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:32:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.23  
% 2.13/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.13/1.23  
% 2.13/1.23  %Foreground sorts:
% 2.13/1.23  
% 2.13/1.23  
% 2.13/1.23  %Background operators:
% 2.13/1.23  
% 2.13/1.23  
% 2.13/1.23  %Foreground operators:
% 2.13/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.13/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.23  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.13/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.13/1.23  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.13/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.13/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.13/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.23  
% 2.26/1.24  tff(f_82, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 2.26/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.26/1.24  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.26/1.24  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.26/1.24  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.26/1.24  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.26/1.24  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.26/1.24  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.26/1.24  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.26/1.24  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.26/1.24  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.26/1.24  tff(c_36, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.26/1.24  tff(c_30, plain, (k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.26/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.26/1.24  tff(c_43, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2])).
% 2.26/1.24  tff(c_32, plain, (m1_setfam_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.26/1.24  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.26/1.24  tff(c_39, plain, (![A_4]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 2.26/1.24  tff(c_86, plain, (![A_29, B_30]: (k5_setfam_1(A_29, B_30)=k3_tarski(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.26/1.24  tff(c_96, plain, (![A_29]: (k5_setfam_1(A_29, '#skF_2')=k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_39, c_86])).
% 2.26/1.24  tff(c_125, plain, (![A_42, B_43]: (m1_subset_1(k5_setfam_1(A_42, B_43), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.26/1.24  tff(c_137, plain, (![A_29]: (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(A_29)) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(superposition, [status(thm), theory('equality')], [c_96, c_125])).
% 2.26/1.24  tff(c_143, plain, (![A_44]: (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(A_44)))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_137])).
% 2.26/1.24  tff(c_18, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.26/1.24  tff(c_156, plain, (![A_45]: (r1_tarski(k3_tarski('#skF_2'), A_45))), inference(resolution, [status(thm)], [c_143, c_18])).
% 2.26/1.24  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.26/1.24  tff(c_41, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10])).
% 2.26/1.24  tff(c_63, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.26/1.24  tff(c_72, plain, (![A_3]: (A_3='#skF_2' | ~r1_tarski(A_3, '#skF_2'))), inference(resolution, [status(thm)], [c_41, c_63])).
% 2.26/1.24  tff(c_168, plain, (k3_tarski('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_156, c_72])).
% 2.26/1.24  tff(c_172, plain, (![A_29]: (k5_setfam_1(A_29, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_96])).
% 2.26/1.24  tff(c_203, plain, (![A_48, B_49]: (k5_setfam_1(A_48, B_49)=A_48 | ~m1_setfam_1(B_49, A_48) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.26/1.24  tff(c_215, plain, (![A_48]: (k5_setfam_1(A_48, '#skF_2')=A_48 | ~m1_setfam_1('#skF_2', A_48))), inference(resolution, [status(thm)], [c_39, c_203])).
% 2.26/1.24  tff(c_220, plain, (![A_50]: (A_50='#skF_2' | ~m1_setfam_1('#skF_2', A_50))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_215])).
% 2.26/1.24  tff(c_224, plain, (u1_struct_0('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_32, c_220])).
% 2.26/1.24  tff(c_28, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.26/1.24  tff(c_229, plain, (~v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_224, c_28])).
% 2.26/1.24  tff(c_233, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_43, c_229])).
% 2.26/1.24  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_233])).
% 2.26/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.24  
% 2.26/1.24  Inference rules
% 2.26/1.24  ----------------------
% 2.26/1.24  #Ref     : 0
% 2.26/1.24  #Sup     : 41
% 2.26/1.24  #Fact    : 0
% 2.26/1.24  #Define  : 0
% 2.26/1.24  #Split   : 0
% 2.26/1.24  #Chain   : 0
% 2.26/1.24  #Close   : 0
% 2.26/1.24  
% 2.26/1.24  Ordering : KBO
% 2.26/1.24  
% 2.26/1.24  Simplification rules
% 2.26/1.24  ----------------------
% 2.26/1.24  #Subsume      : 0
% 2.26/1.24  #Demod        : 20
% 2.26/1.24  #Tautology    : 22
% 2.26/1.24  #SimpNegUnit  : 1
% 2.26/1.24  #BackRed      : 4
% 2.26/1.24  
% 2.26/1.24  #Partial instantiations: 0
% 2.26/1.24  #Strategies tried      : 1
% 2.26/1.24  
% 2.26/1.24  Timing (in seconds)
% 2.26/1.24  ----------------------
% 2.26/1.25  Preprocessing        : 0.31
% 2.26/1.25  Parsing              : 0.17
% 2.26/1.25  CNF conversion       : 0.02
% 2.26/1.25  Main loop            : 0.16
% 2.26/1.25  Inferencing          : 0.06
% 2.26/1.25  Reduction            : 0.06
% 2.26/1.25  Demodulation         : 0.04
% 2.26/1.25  BG Simplification    : 0.01
% 2.26/1.25  Subsumption          : 0.03
% 2.26/1.25  Abstraction          : 0.01
% 2.26/1.25  MUC search           : 0.00
% 2.26/1.25  Cooper               : 0.00
% 2.26/1.25  Total                : 0.51
% 2.26/1.25  Index Insertion      : 0.00
% 2.26/1.25  Index Deletion       : 0.00
% 2.26/1.25  Index Matching       : 0.00
% 2.26/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
