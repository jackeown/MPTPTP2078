%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:29 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   51 (  76 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 119 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_31,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_26,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8])).

tff(c_87,plain,(
    ! [C_34,B_35,A_36] :
      ( v1_xboole_0(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(B_35,A_36)))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_98,plain,(
    ! [A_36] :
      ( v1_xboole_0('#skF_3')
      | ~ v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_34,c_87])).

tff(c_99,plain,(
    ! [A_36] : ~ v1_xboole_0(A_36) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_4,plain,(
    ! [A_1] : v1_xboole_0('#skF_1'(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_4])).

tff(c_103,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_26,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_37,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_2])).

tff(c_50,plain,(
    ! [A_23,B_24] :
      ( k5_setfam_1(A_23,B_24) = k3_tarski(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    ! [A_23] : k5_setfam_1(A_23,'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_61,plain,(
    ! [A_23] : k5_setfam_1(A_23,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_58])).

tff(c_120,plain,(
    ! [A_41,B_42] :
      ( k5_setfam_1(A_41,B_42) = A_41
      | ~ m1_setfam_1(B_42,A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_128,plain,(
    ! [A_41] :
      ( k5_setfam_1(A_41,'#skF_3') = A_41
      | ~ m1_setfam_1('#skF_3',A_41) ) ),
    inference(resolution,[status(thm)],[c_34,c_120])).

tff(c_133,plain,(
    ! [A_43] :
      ( A_43 = '#skF_3'
      | ~ m1_setfam_1('#skF_3',A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_128])).

tff(c_141,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_133])).

tff(c_22,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_147,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_22])).

tff(c_151,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_103,c_147])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:46:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  %$ r2_hidden > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.91/1.20  
% 1.91/1.20  %Foreground sorts:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Background operators:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Foreground operators:
% 1.91/1.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.91/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.20  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.91/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.91/1.20  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.91/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.91/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.20  
% 1.91/1.22  tff(f_80, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 1.91/1.22  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.91/1.22  tff(f_56, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 1.91/1.22  tff(f_31, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 1.91/1.22  tff(f_26, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.91/1.22  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 1.91/1.22  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 1.91/1.22  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.91/1.22  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.22  tff(c_30, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.22  tff(c_24, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.22  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.22  tff(c_34, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_8])).
% 1.91/1.22  tff(c_87, plain, (![C_34, B_35, A_36]: (v1_xboole_0(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(B_35, A_36))) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.91/1.22  tff(c_98, plain, (![A_36]: (v1_xboole_0('#skF_3') | ~v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_34, c_87])).
% 1.91/1.22  tff(c_99, plain, (![A_36]: (~v1_xboole_0(A_36))), inference(splitLeft, [status(thm)], [c_98])).
% 1.91/1.22  tff(c_4, plain, (![A_1]: (v1_xboole_0('#skF_1'(A_1)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.22  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_4])).
% 1.91/1.22  tff(c_103, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_98])).
% 1.91/1.22  tff(c_26, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.22  tff(c_2, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.91/1.22  tff(c_37, plain, (k3_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_2])).
% 1.91/1.22  tff(c_50, plain, (![A_23, B_24]: (k5_setfam_1(A_23, B_24)=k3_tarski(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_23))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.22  tff(c_58, plain, (![A_23]: (k5_setfam_1(A_23, '#skF_3')=k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_50])).
% 1.91/1.22  tff(c_61, plain, (![A_23]: (k5_setfam_1(A_23, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_58])).
% 1.91/1.22  tff(c_120, plain, (![A_41, B_42]: (k5_setfam_1(A_41, B_42)=A_41 | ~m1_setfam_1(B_42, A_41) | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_41))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.91/1.22  tff(c_128, plain, (![A_41]: (k5_setfam_1(A_41, '#skF_3')=A_41 | ~m1_setfam_1('#skF_3', A_41))), inference(resolution, [status(thm)], [c_34, c_120])).
% 1.91/1.22  tff(c_133, plain, (![A_43]: (A_43='#skF_3' | ~m1_setfam_1('#skF_3', A_43))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_128])).
% 1.91/1.22  tff(c_141, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_26, c_133])).
% 1.91/1.22  tff(c_22, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.91/1.22  tff(c_147, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_141, c_22])).
% 1.91/1.22  tff(c_151, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_103, c_147])).
% 1.91/1.22  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_151])).
% 1.91/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  Inference rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Ref     : 0
% 1.91/1.22  #Sup     : 23
% 1.91/1.22  #Fact    : 0
% 1.91/1.22  #Define  : 0
% 1.91/1.22  #Split   : 1
% 1.91/1.22  #Chain   : 0
% 1.91/1.22  #Close   : 0
% 1.91/1.22  
% 1.91/1.22  Ordering : KBO
% 1.91/1.22  
% 1.91/1.22  Simplification rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Subsume      : 2
% 1.91/1.22  #Demod        : 16
% 1.91/1.22  #Tautology    : 14
% 1.91/1.22  #SimpNegUnit  : 3
% 1.91/1.22  #BackRed      : 2
% 1.91/1.22  
% 1.91/1.22  #Partial instantiations: 0
% 1.91/1.22  #Strategies tried      : 1
% 1.91/1.22  
% 1.91/1.22  Timing (in seconds)
% 1.91/1.22  ----------------------
% 1.91/1.22  Preprocessing        : 0.30
% 1.91/1.22  Parsing              : 0.16
% 1.91/1.22  CNF conversion       : 0.02
% 1.91/1.22  Main loop            : 0.14
% 1.91/1.22  Inferencing          : 0.05
% 1.91/1.22  Reduction            : 0.05
% 1.91/1.22  Demodulation         : 0.04
% 1.91/1.22  BG Simplification    : 0.01
% 1.91/1.22  Subsumption          : 0.02
% 1.91/1.22  Abstraction          : 0.01
% 1.91/1.22  MUC search           : 0.00
% 1.91/1.22  Cooper               : 0.00
% 1.91/1.22  Total                : 0.47
% 1.91/1.22  Index Insertion      : 0.00
% 1.91/1.22  Index Deletion       : 0.00
% 1.91/1.22  Index Matching       : 0.00
% 1.91/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
