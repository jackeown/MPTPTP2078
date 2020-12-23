%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:31 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 (  95 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_41,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    m1_setfam_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12])).

tff(c_46,plain,(
    ! [A_22] :
      ( v1_xboole_0(A_22)
      | r2_hidden('#skF_1'(A_22),A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    ! [A_23] :
      ( ~ r1_tarski(A_23,'#skF_1'(A_23))
      | v1_xboole_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_46,c_20])).

tff(c_60,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_55])).

tff(c_14,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_33,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_14])).

tff(c_72,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,k3_tarski(B_29))
      | ~ m1_setfam_1(B_29,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,'#skF_4')
      | ~ m1_setfam_1('#skF_4',A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_72])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_142,plain,(
    ! [C_43,B_44,A_45] :
      ( r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_161,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48),B_49)
      | ~ r1_tarski(A_48,B_49)
      | v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_4,c_142])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    ! [B_50,A_51] :
      ( ~ v1_xboole_0(B_50)
      | ~ r1_tarski(A_51,B_50)
      | v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_161,c_2])).

tff(c_182,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0('#skF_4')
      | v1_xboole_0(A_28)
      | ~ m1_setfam_1('#skF_4',A_28) ) ),
    inference(resolution,[status(thm)],[c_78,c_173])).

tff(c_202,plain,(
    ! [A_54] :
      ( v1_xboole_0(A_54)
      | ~ m1_setfam_1('#skF_4',A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_182])).

tff(c_223,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_202])).

tff(c_22,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_226,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_223,c_22])).

tff(c_229,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_226])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:16:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
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
% 1.93/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.93/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.19  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.93/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.19  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.93/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.93/1.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.93/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.19  
% 1.93/1.20  tff(f_72, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 1.93/1.20  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.93/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.93/1.20  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.93/1.20  tff(f_41, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.93/1.20  tff(f_45, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.93/1.20  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.93/1.20  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.93/1.20  tff(c_32, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.20  tff(c_30, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.20  tff(c_26, plain, (m1_setfam_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.20  tff(c_24, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.20  tff(c_12, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.93/1.20  tff(c_34, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12])).
% 1.93/1.20  tff(c_46, plain, (![A_22]: (v1_xboole_0(A_22) | r2_hidden('#skF_1'(A_22), A_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.20  tff(c_20, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.20  tff(c_55, plain, (![A_23]: (~r1_tarski(A_23, '#skF_1'(A_23)) | v1_xboole_0(A_23))), inference(resolution, [status(thm)], [c_46, c_20])).
% 1.93/1.20  tff(c_60, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_55])).
% 1.93/1.20  tff(c_14, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.20  tff(c_33, plain, (k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_14])).
% 1.93/1.20  tff(c_72, plain, (![A_28, B_29]: (r1_tarski(A_28, k3_tarski(B_29)) | ~m1_setfam_1(B_29, A_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.20  tff(c_78, plain, (![A_28]: (r1_tarski(A_28, '#skF_4') | ~m1_setfam_1('#skF_4', A_28))), inference(superposition, [status(thm), theory('equality')], [c_33, c_72])).
% 1.93/1.20  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.20  tff(c_142, plain, (![C_43, B_44, A_45]: (r2_hidden(C_43, B_44) | ~r2_hidden(C_43, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.20  tff(c_161, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48), B_49) | ~r1_tarski(A_48, B_49) | v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_4, c_142])).
% 1.93/1.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.20  tff(c_173, plain, (![B_50, A_51]: (~v1_xboole_0(B_50) | ~r1_tarski(A_51, B_50) | v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_161, c_2])).
% 1.93/1.20  tff(c_182, plain, (![A_28]: (~v1_xboole_0('#skF_4') | v1_xboole_0(A_28) | ~m1_setfam_1('#skF_4', A_28))), inference(resolution, [status(thm)], [c_78, c_173])).
% 1.93/1.20  tff(c_202, plain, (![A_54]: (v1_xboole_0(A_54) | ~m1_setfam_1('#skF_4', A_54))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_182])).
% 1.93/1.20  tff(c_223, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_202])).
% 1.93/1.20  tff(c_22, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.20  tff(c_226, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_223, c_22])).
% 1.93/1.20  tff(c_229, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_226])).
% 1.93/1.20  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_229])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 40
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
% 1.93/1.20  #Tautology    : 18
% 1.93/1.20  #SimpNegUnit  : 1
% 1.93/1.20  #BackRed      : 0
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.20  Preprocessing        : 0.27
% 1.93/1.20  Parsing              : 0.15
% 1.93/1.20  CNF conversion       : 0.02
% 1.93/1.20  Main loop            : 0.16
% 1.93/1.20  Inferencing          : 0.07
% 1.93/1.20  Reduction            : 0.05
% 1.93/1.20  Demodulation         : 0.03
% 1.93/1.20  BG Simplification    : 0.01
% 1.93/1.20  Subsumption          : 0.03
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.47
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
