%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:06 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 139 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 ( 230 expanded)
%              Number of equality atoms :   17 (  78 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_29,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_24])).

tff(c_56,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_64,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_29,c_56])).

tff(c_76,plain,(
    ! [B_22,A_23] :
      ( B_22 = A_23
      | ~ r1_tarski(B_22,A_23)
      | ~ r1_tarski(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_76])).

tff(c_85,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_98,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_8])).

tff(c_94,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_85,c_14])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( m1_subset_1(k8_relset_1(A_25,B_26,C_27,D_28),k1_zfmisc_1(A_25))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_165,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( r1_tarski(k8_relset_1(A_34,B_35,C_36,D_37),A_34)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(resolution,[status(thm)],[c_108,c_16])).

tff(c_178,plain,(
    ! [A_38,B_39,A_40,D_41] :
      ( r1_tarski(k8_relset_1(A_38,B_39,A_40,D_41),A_38)
      | ~ r1_tarski(A_40,k2_zfmisc_1(A_38,B_39)) ) ),
    inference(resolution,[status(thm)],[c_18,c_165])).

tff(c_90,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_140,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_85,c_90])).

tff(c_182,plain,(
    ! [B_39,A_40,D_41] :
      ( k8_relset_1('#skF_3',B_39,A_40,D_41) = '#skF_3'
      | ~ r1_tarski(A_40,k2_zfmisc_1('#skF_3',B_39)) ) ),
    inference(resolution,[status(thm)],[c_178,c_140])).

tff(c_188,plain,(
    ! [B_42,A_43,D_44] :
      ( k8_relset_1('#skF_3',B_42,A_43,D_44) = '#skF_3'
      | ~ r1_tarski(A_43,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_182])).

tff(c_200,plain,(
    ! [B_42,D_44] : k8_relset_1('#skF_3',B_42,'#skF_3',D_44) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_98,c_188])).

tff(c_22,plain,(
    k8_relset_1(k1_xboole_0,'#skF_1','#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_93,plain,(
    k8_relset_1('#skF_3','#skF_1','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_85,c_22])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.60  
% 2.26/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.61  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.26/1.61  
% 2.26/1.61  %Foreground sorts:
% 2.26/1.61  
% 2.26/1.61  
% 2.26/1.61  %Background operators:
% 2.26/1.61  
% 2.26/1.61  
% 2.26/1.61  %Foreground operators:
% 2.26/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.61  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.26/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.26/1.61  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.61  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.61  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.61  
% 2.38/1.63  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.38/1.63  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.38/1.63  tff(f_56, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.38/1.63  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.38/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.38/1.63  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 2.38/1.63  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.38/1.63  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.38/1.63  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.38/1.63  tff(c_29, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_24])).
% 2.38/1.63  tff(c_56, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.63  tff(c_64, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_29, c_56])).
% 2.38/1.63  tff(c_76, plain, (![B_22, A_23]: (B_22=A_23 | ~r1_tarski(B_22, A_23) | ~r1_tarski(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.63  tff(c_78, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_64, c_76])).
% 2.38/1.63  tff(c_85, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_78])).
% 2.38/1.63  tff(c_98, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_8])).
% 2.38/1.63  tff(c_94, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_85, c_14])).
% 2.38/1.63  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.63  tff(c_108, plain, (![A_25, B_26, C_27, D_28]: (m1_subset_1(k8_relset_1(A_25, B_26, C_27, D_28), k1_zfmisc_1(A_25)) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.38/1.63  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.63  tff(c_165, plain, (![A_34, B_35, C_36, D_37]: (r1_tarski(k8_relset_1(A_34, B_35, C_36, D_37), A_34) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(resolution, [status(thm)], [c_108, c_16])).
% 2.38/1.63  tff(c_178, plain, (![A_38, B_39, A_40, D_41]: (r1_tarski(k8_relset_1(A_38, B_39, A_40, D_41), A_38) | ~r1_tarski(A_40, k2_zfmisc_1(A_38, B_39)))), inference(resolution, [status(thm)], [c_18, c_165])).
% 2.38/1.63  tff(c_90, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_76])).
% 2.38/1.63  tff(c_140, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_85, c_90])).
% 2.38/1.63  tff(c_182, plain, (![B_39, A_40, D_41]: (k8_relset_1('#skF_3', B_39, A_40, D_41)='#skF_3' | ~r1_tarski(A_40, k2_zfmisc_1('#skF_3', B_39)))), inference(resolution, [status(thm)], [c_178, c_140])).
% 2.38/1.63  tff(c_188, plain, (![B_42, A_43, D_44]: (k8_relset_1('#skF_3', B_42, A_43, D_44)='#skF_3' | ~r1_tarski(A_43, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_182])).
% 2.38/1.63  tff(c_200, plain, (![B_42, D_44]: (k8_relset_1('#skF_3', B_42, '#skF_3', D_44)='#skF_3')), inference(resolution, [status(thm)], [c_98, c_188])).
% 2.38/1.63  tff(c_22, plain, (k8_relset_1(k1_xboole_0, '#skF_1', '#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.38/1.63  tff(c_93, plain, (k8_relset_1('#skF_3', '#skF_1', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_85, c_22])).
% 2.38/1.63  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_93])).
% 2.38/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.63  
% 2.38/1.63  Inference rules
% 2.38/1.63  ----------------------
% 2.38/1.63  #Ref     : 0
% 2.38/1.63  #Sup     : 37
% 2.38/1.63  #Fact    : 0
% 2.38/1.63  #Define  : 0
% 2.38/1.63  #Split   : 0
% 2.38/1.63  #Chain   : 0
% 2.38/1.63  #Close   : 0
% 2.38/1.63  
% 2.38/1.63  Ordering : KBO
% 2.38/1.63  
% 2.38/1.63  Simplification rules
% 2.38/1.63  ----------------------
% 2.38/1.63  #Subsume      : 1
% 2.38/1.63  #Demod        : 24
% 2.38/1.63  #Tautology    : 25
% 2.38/1.63  #SimpNegUnit  : 0
% 2.38/1.63  #BackRed      : 9
% 2.38/1.63  
% 2.38/1.63  #Partial instantiations: 0
% 2.38/1.63  #Strategies tried      : 1
% 2.38/1.63  
% 2.38/1.63  Timing (in seconds)
% 2.38/1.63  ----------------------
% 2.38/1.63  Preprocessing        : 0.43
% 2.38/1.63  Parsing              : 0.23
% 2.38/1.63  CNF conversion       : 0.03
% 2.38/1.63  Main loop            : 0.26
% 2.38/1.63  Inferencing          : 0.10
% 2.38/1.63  Reduction            : 0.08
% 2.38/1.63  Demodulation         : 0.06
% 2.38/1.63  BG Simplification    : 0.02
% 2.38/1.63  Subsumption          : 0.05
% 2.38/1.63  Abstraction          : 0.01
% 2.38/1.63  MUC search           : 0.00
% 2.38/1.63  Cooper               : 0.00
% 2.38/1.63  Total                : 0.74
% 2.38/1.63  Index Insertion      : 0.00
% 2.38/1.63  Index Deletion       : 0.00
% 2.38/1.63  Index Matching       : 0.00
% 2.38/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
