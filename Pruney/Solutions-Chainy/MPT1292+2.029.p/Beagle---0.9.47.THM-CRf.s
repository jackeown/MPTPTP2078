%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:33 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   53 (  68 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   68 ( 123 expanded)
%              Number of equality atoms :   12 (  27 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
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

tff(f_63,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2])).

tff(c_26,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_33,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_16])).

tff(c_57,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,k3_tarski(B_20))
      | ~ m1_setfam_1(B_20,A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_63,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,'#skF_3')
      | ~ m1_setfam_1('#skF_3',A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_57])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_35,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_12])).

tff(c_86,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ r1_xboole_0(A_30,B_31)
      | ~ r2_hidden(C_32,B_31)
      | ~ r2_hidden(C_32,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,(
    ! [C_33] : ~ r2_hidden(C_33,'#skF_3') ),
    inference(resolution,[status(thm)],[c_35,c_86])).

tff(c_105,plain,(
    ! [B_34] : r1_xboole_0('#skF_3',B_34) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,C_8)
      | ~ r1_xboole_0(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_133,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(A_36,B_37)
      | ~ r1_tarski(A_36,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_105,c_10])).

tff(c_14,plain,(
    ! [A_9] :
      ( ~ r1_xboole_0(A_9,A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [A_9] :
      ( ~ r1_xboole_0(A_9,A_9)
      | A_9 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14])).

tff(c_145,plain,(
    ! [B_38] :
      ( B_38 = '#skF_3'
      | ~ r1_tarski(B_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_133,c_34])).

tff(c_150,plain,(
    ! [A_39] :
      ( A_39 = '#skF_3'
      | ~ m1_setfam_1('#skF_3',A_39) ) ),
    inference(resolution,[status(thm)],[c_63,c_145])).

tff(c_154,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_150])).

tff(c_22,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_161,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_22])).

tff(c_165,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36,c_161])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n021.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 18:02:04 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.19  
% 1.93/1.19  %Foreground sorts:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Background operators:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Foreground operators:
% 1.93/1.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.19  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.93/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.19  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.93/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.93/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.19  
% 1.93/1.20  tff(f_89, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 1.93/1.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.93/1.20  tff(f_63, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.93/1.20  tff(f_67, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.93/1.20  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.93/1.20  tff(f_62, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.93/1.20  tff(f_50, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.93/1.20  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.93/1.20  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.93/1.20  tff(c_30, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.93/1.20  tff(c_24, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.93/1.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.93/1.20  tff(c_36, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2])).
% 1.93/1.20  tff(c_26, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.93/1.20  tff(c_16, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.20  tff(c_33, plain, (k3_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_16])).
% 1.93/1.20  tff(c_57, plain, (![A_19, B_20]: (r1_tarski(A_19, k3_tarski(B_20)) | ~m1_setfam_1(B_20, A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.93/1.20  tff(c_63, plain, (![A_19]: (r1_tarski(A_19, '#skF_3') | ~m1_setfam_1('#skF_3', A_19))), inference(superposition, [status(thm), theory('equality')], [c_33, c_57])).
% 1.93/1.20  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.20  tff(c_12, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.93/1.20  tff(c_35, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_12])).
% 1.93/1.20  tff(c_86, plain, (![A_30, B_31, C_32]: (~r1_xboole_0(A_30, B_31) | ~r2_hidden(C_32, B_31) | ~r2_hidden(C_32, A_30))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.20  tff(c_93, plain, (![C_33]: (~r2_hidden(C_33, '#skF_3'))), inference(resolution, [status(thm)], [c_35, c_86])).
% 1.93/1.20  tff(c_105, plain, (![B_34]: (r1_xboole_0('#skF_3', B_34))), inference(resolution, [status(thm)], [c_8, c_93])).
% 1.93/1.20  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, C_8) | ~r1_xboole_0(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.20  tff(c_133, plain, (![A_36, B_37]: (r1_xboole_0(A_36, B_37) | ~r1_tarski(A_36, '#skF_3'))), inference(resolution, [status(thm)], [c_105, c_10])).
% 1.93/1.20  tff(c_14, plain, (![A_9]: (~r1_xboole_0(A_9, A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.93/1.20  tff(c_34, plain, (![A_9]: (~r1_xboole_0(A_9, A_9) | A_9='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14])).
% 1.93/1.20  tff(c_145, plain, (![B_38]: (B_38='#skF_3' | ~r1_tarski(B_38, '#skF_3'))), inference(resolution, [status(thm)], [c_133, c_34])).
% 1.93/1.20  tff(c_150, plain, (![A_39]: (A_39='#skF_3' | ~m1_setfam_1('#skF_3', A_39))), inference(resolution, [status(thm)], [c_63, c_145])).
% 1.93/1.20  tff(c_154, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_26, c_150])).
% 1.93/1.20  tff(c_22, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.20  tff(c_161, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_154, c_22])).
% 1.93/1.20  tff(c_165, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_36, c_161])).
% 1.93/1.20  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_165])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 30
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 0
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 2
% 1.93/1.20  #Demod        : 14
% 1.93/1.20  #Tautology    : 15
% 1.93/1.20  #SimpNegUnit  : 1
% 1.93/1.20  #BackRed      : 2
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 2.01/1.21  Preprocessing        : 0.32
% 2.01/1.21  Parsing              : 0.17
% 2.01/1.21  CNF conversion       : 0.02
% 2.01/1.21  Main loop            : 0.14
% 2.01/1.21  Inferencing          : 0.05
% 2.01/1.21  Reduction            : 0.04
% 2.01/1.21  Demodulation         : 0.03
% 2.01/1.21  BG Simplification    : 0.01
% 2.01/1.21  Subsumption          : 0.02
% 2.01/1.21  Abstraction          : 0.01
% 2.01/1.21  MUC search           : 0.00
% 2.01/1.21  Cooper               : 0.00
% 2.01/1.21  Total                : 0.48
% 2.01/1.21  Index Insertion      : 0.00
% 2.01/1.21  Index Deletion       : 0.00
% 2.01/1.21  Index Matching       : 0.00
% 2.01/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
