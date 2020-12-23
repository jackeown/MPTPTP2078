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
% DateTime   : Thu Dec  3 10:22:30 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   53 (  64 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 ( 106 expanded)
%              Number of equality atoms :   12 (  23 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_49,axiom,(
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

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    m1_setfam_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [A_12] : r1_tarski('#skF_4',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_18])).

tff(c_24,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_41,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_24])).

tff(c_88,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,k3_tarski(B_29))
      | ~ m1_setfam_1(B_29,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_94,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,'#skF_4')
      | ~ m1_setfam_1('#skF_4',A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_88])).

tff(c_115,plain,(
    ! [B_33,A_34] :
      ( B_33 = A_34
      | ~ r1_tarski(B_33,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_117,plain,(
    ! [A_28] :
      ( A_28 = '#skF_4'
      | ~ r1_tarski('#skF_4',A_28)
      | ~ m1_setfam_1('#skF_4',A_28) ) ),
    inference(resolution,[status(thm)],[c_94,c_115])).

tff(c_150,plain,(
    ! [A_36] :
      ( A_36 = '#skF_4'
      | ~ m1_setfam_1('#skF_4',A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_117])).

tff(c_166,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_150])).

tff(c_30,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_173,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_30])).

tff(c_177,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_173])).

tff(c_178,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_177])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_43,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_20])).

tff(c_203,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,B_47)
      | ~ r2_hidden(C_48,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_213,plain,(
    ! [C_49] : ~ r2_hidden(C_49,'#skF_4') ),
    inference(resolution,[status(thm)],[c_43,c_203])).

tff(c_225,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_213])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:12:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.27  
% 2.38/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.27  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.38/1.27  
% 2.38/1.27  %Foreground sorts:
% 2.38/1.27  
% 2.38/1.27  
% 2.38/1.27  %Background operators:
% 2.38/1.27  
% 2.38/1.27  
% 2.38/1.27  %Foreground operators:
% 2.38/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.38/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.38/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.38/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.27  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.38/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.38/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.38/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.38/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.38/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.27  
% 2.38/1.29  tff(f_96, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 2.38/1.29  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.38/1.29  tff(f_70, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.38/1.29  tff(f_74, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.38/1.29  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.38/1.29  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.38/1.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.38/1.29  tff(f_69, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.38/1.29  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.38/1.29  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.38/1.29  tff(c_38, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.38/1.29  tff(c_34, plain, (m1_setfam_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.38/1.29  tff(c_32, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.38/1.29  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.38/1.29  tff(c_44, plain, (![A_12]: (r1_tarski('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_18])).
% 2.38/1.29  tff(c_24, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.38/1.29  tff(c_41, plain, (k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_24])).
% 2.38/1.29  tff(c_88, plain, (![A_28, B_29]: (r1_tarski(A_28, k3_tarski(B_29)) | ~m1_setfam_1(B_29, A_28))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.38/1.29  tff(c_94, plain, (![A_28]: (r1_tarski(A_28, '#skF_4') | ~m1_setfam_1('#skF_4', A_28))), inference(superposition, [status(thm), theory('equality')], [c_41, c_88])).
% 2.38/1.29  tff(c_115, plain, (![B_33, A_34]: (B_33=A_34 | ~r1_tarski(B_33, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.38/1.29  tff(c_117, plain, (![A_28]: (A_28='#skF_4' | ~r1_tarski('#skF_4', A_28) | ~m1_setfam_1('#skF_4', A_28))), inference(resolution, [status(thm)], [c_94, c_115])).
% 2.38/1.29  tff(c_150, plain, (![A_36]: (A_36='#skF_4' | ~m1_setfam_1('#skF_4', A_36))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_117])).
% 2.38/1.29  tff(c_166, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_150])).
% 2.38/1.29  tff(c_30, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.38/1.29  tff(c_173, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_166, c_30])).
% 2.38/1.29  tff(c_177, plain, (~v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_173])).
% 2.38/1.29  tff(c_178, plain, (~v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_177])).
% 2.38/1.29  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.29  tff(c_20, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.38/1.29  tff(c_43, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_20])).
% 2.38/1.29  tff(c_203, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, B_47) | ~r2_hidden(C_48, A_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.29  tff(c_213, plain, (![C_49]: (~r2_hidden(C_49, '#skF_4'))), inference(resolution, [status(thm)], [c_43, c_203])).
% 2.38/1.29  tff(c_225, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_213])).
% 2.38/1.29  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_225])).
% 2.38/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.29  
% 2.38/1.29  Inference rules
% 2.38/1.29  ----------------------
% 2.38/1.29  #Ref     : 0
% 2.38/1.29  #Sup     : 38
% 2.38/1.29  #Fact    : 0
% 2.38/1.29  #Define  : 0
% 2.38/1.29  #Split   : 0
% 2.38/1.29  #Chain   : 0
% 2.38/1.29  #Close   : 0
% 2.38/1.29  
% 2.38/1.29  Ordering : KBO
% 2.38/1.29  
% 2.38/1.29  Simplification rules
% 2.38/1.29  ----------------------
% 2.38/1.29  #Subsume      : 4
% 2.38/1.29  #Demod        : 17
% 2.38/1.29  #Tautology    : 20
% 2.38/1.29  #SimpNegUnit  : 2
% 2.38/1.29  #BackRed      : 2
% 2.38/1.29  
% 2.38/1.29  #Partial instantiations: 0
% 2.38/1.29  #Strategies tried      : 1
% 2.38/1.29  
% 2.38/1.29  Timing (in seconds)
% 2.38/1.29  ----------------------
% 2.38/1.29  Preprocessing        : 0.32
% 2.38/1.29  Parsing              : 0.18
% 2.38/1.29  CNF conversion       : 0.02
% 2.38/1.29  Main loop            : 0.16
% 2.38/1.29  Inferencing          : 0.06
% 2.38/1.29  Reduction            : 0.05
% 2.38/1.29  Demodulation         : 0.04
% 2.38/1.29  BG Simplification    : 0.01
% 2.38/1.29  Subsumption          : 0.03
% 2.38/1.29  Abstraction          : 0.01
% 2.38/1.29  MUC search           : 0.00
% 2.38/1.30  Cooper               : 0.00
% 2.38/1.30  Total                : 0.52
% 2.38/1.30  Index Insertion      : 0.00
% 2.38/1.30  Index Deletion       : 0.00
% 2.38/1.30  Index Matching       : 0.00
% 2.38/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
