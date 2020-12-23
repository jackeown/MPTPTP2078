%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:34 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   53 (  67 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 ( 105 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
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

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_30,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_41,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2])).

tff(c_28,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_40,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_22,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_1'(A_13),A_13)
      | k3_tarski(A_13) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_59,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_1'(A_24),A_24)
      | k3_tarski(A_24) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    ! [A_25] :
      ( ~ r1_tarski(A_25,'#skF_1'(A_25))
      | k3_tarski(A_25) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_59,c_16])).

tff(c_69,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_40,c_64])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_38,plain,(
    ! [A_2] : m1_subset_1('#skF_3',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6])).

tff(c_91,plain,(
    ! [A_31,B_32] :
      ( k5_setfam_1(A_31,B_32) = k3_tarski(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_95,plain,(
    ! [A_31] : k5_setfam_1(A_31,'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_91])).

tff(c_97,plain,(
    ! [A_31] : k5_setfam_1(A_31,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_95])).

tff(c_111,plain,(
    ! [A_36,B_37] :
      ( k5_setfam_1(A_36,B_37) = A_36
      | ~ m1_setfam_1(B_37,A_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_115,plain,(
    ! [A_36] :
      ( k5_setfam_1(A_36,'#skF_3') = A_36
      | ~ m1_setfam_1('#skF_3',A_36) ) ),
    inference(resolution,[status(thm)],[c_38,c_111])).

tff(c_125,plain,(
    ! [A_40] :
      ( A_40 = '#skF_3'
      | ~ m1_setfam_1('#skF_3',A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_115])).

tff(c_129,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_125])).

tff(c_18,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_134,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_18])).

tff(c_138,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_41,c_134])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:51:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.16  
% 1.88/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.16  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.88/1.16  
% 1.88/1.16  %Foreground sorts:
% 1.88/1.16  
% 1.88/1.16  
% 1.88/1.16  %Background operators:
% 1.88/1.16  
% 1.88/1.16  
% 1.88/1.16  %Foreground operators:
% 1.88/1.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.88/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.88/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.16  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.88/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.16  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.88/1.16  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.88/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.88/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.88/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.16  
% 1.88/1.17  tff(f_93, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 1.88/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.88/1.17  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.88/1.17  tff(f_79, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 1.88/1.17  tff(f_51, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.88/1.17  tff(f_30, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.88/1.17  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 1.88/1.17  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 1.88/1.17  tff(f_59, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.88/1.17  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.88/1.17  tff(c_32, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.88/1.17  tff(c_26, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.88/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.88/1.17  tff(c_41, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2])).
% 1.88/1.17  tff(c_28, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.88/1.17  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.88/1.17  tff(c_40, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4])).
% 1.88/1.17  tff(c_22, plain, (![A_13]: (r2_hidden('#skF_1'(A_13), A_13) | k3_tarski(A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.88/1.17  tff(c_59, plain, (![A_24]: (r2_hidden('#skF_1'(A_24), A_24) | k3_tarski(A_24)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22])).
% 1.88/1.17  tff(c_16, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.17  tff(c_64, plain, (![A_25]: (~r1_tarski(A_25, '#skF_1'(A_25)) | k3_tarski(A_25)='#skF_3')), inference(resolution, [status(thm)], [c_59, c_16])).
% 1.88/1.17  tff(c_69, plain, (k3_tarski('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_40, c_64])).
% 1.88/1.17  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.88/1.17  tff(c_38, plain, (![A_2]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6])).
% 1.88/1.17  tff(c_91, plain, (![A_31, B_32]: (k5_setfam_1(A_31, B_32)=k3_tarski(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(k1_zfmisc_1(A_31))))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.88/1.17  tff(c_95, plain, (![A_31]: (k5_setfam_1(A_31, '#skF_3')=k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_91])).
% 1.88/1.17  tff(c_97, plain, (![A_31]: (k5_setfam_1(A_31, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_95])).
% 1.88/1.17  tff(c_111, plain, (![A_36, B_37]: (k5_setfam_1(A_36, B_37)=A_36 | ~m1_setfam_1(B_37, A_36) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.88/1.17  tff(c_115, plain, (![A_36]: (k5_setfam_1(A_36, '#skF_3')=A_36 | ~m1_setfam_1('#skF_3', A_36))), inference(resolution, [status(thm)], [c_38, c_111])).
% 1.88/1.17  tff(c_125, plain, (![A_40]: (A_40='#skF_3' | ~m1_setfam_1('#skF_3', A_40))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_115])).
% 1.88/1.17  tff(c_129, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_125])).
% 1.88/1.17  tff(c_18, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.88/1.17  tff(c_134, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_129, c_18])).
% 1.88/1.17  tff(c_138, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_41, c_134])).
% 1.88/1.17  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_138])).
% 1.88/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  Inference rules
% 1.88/1.17  ----------------------
% 1.88/1.17  #Ref     : 0
% 1.88/1.17  #Sup     : 22
% 1.88/1.17  #Fact    : 0
% 1.88/1.17  #Define  : 0
% 1.88/1.17  #Split   : 0
% 1.88/1.17  #Chain   : 0
% 1.88/1.17  #Close   : 0
% 1.88/1.17  
% 1.88/1.17  Ordering : KBO
% 1.88/1.17  
% 1.88/1.17  Simplification rules
% 1.88/1.17  ----------------------
% 1.88/1.17  #Subsume      : 0
% 1.88/1.17  #Demod        : 16
% 1.88/1.17  #Tautology    : 14
% 1.88/1.17  #SimpNegUnit  : 1
% 1.88/1.17  #BackRed      : 1
% 1.88/1.17  
% 1.88/1.17  #Partial instantiations: 0
% 1.88/1.17  #Strategies tried      : 1
% 1.88/1.17  
% 1.88/1.17  Timing (in seconds)
% 1.88/1.17  ----------------------
% 1.88/1.18  Preprocessing        : 0.29
% 1.88/1.18  Parsing              : 0.15
% 1.88/1.18  CNF conversion       : 0.02
% 1.88/1.18  Main loop            : 0.12
% 1.88/1.18  Inferencing          : 0.05
% 1.88/1.18  Reduction            : 0.04
% 1.88/1.18  Demodulation         : 0.03
% 1.88/1.18  BG Simplification    : 0.01
% 1.88/1.18  Subsumption          : 0.02
% 1.88/1.18  Abstraction          : 0.01
% 1.88/1.18  MUC search           : 0.00
% 1.88/1.18  Cooper               : 0.00
% 1.88/1.18  Total                : 0.44
% 1.88/1.18  Index Insertion      : 0.00
% 1.88/1.18  Index Deletion       : 0.00
% 1.88/1.18  Index Matching       : 0.00
% 1.88/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
