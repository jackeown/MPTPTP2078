%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:20 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 106 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 167 expanded)
%              Number of equality atoms :    8 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_69,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(B_36,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_69])).

tff(c_16,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    ! [B_36,A_35] : k3_xboole_0(B_36,A_35) = k3_xboole_0(A_35,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_16])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski(A_43,B_44)
      | ~ r1_tarski(A_43,k3_xboole_0(B_44,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_178,plain,(
    ! [B_44,C_45] : r1_tarski(k3_xboole_0(B_44,C_45),B_44) ),
    inference(resolution,[status(thm)],[c_6,c_167])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_162,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_230,plain,(
    ! [A_53,B_54] :
      ( v1_relat_1(A_53)
      | ~ v1_relat_1(B_54)
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_20,c_162])).

tff(c_247,plain,(
    ! [B_55,C_56] :
      ( v1_relat_1(k3_xboole_0(B_55,C_56))
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_178,c_230])).

tff(c_250,plain,(
    ! [B_36,A_35] :
      ( v1_relat_1(k3_xboole_0(B_36,A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_247])).

tff(c_179,plain,(
    ! [B_46,C_47] : r1_tarski(k3_xboole_0(B_46,C_47),B_46) ),
    inference(resolution,[status(thm)],[c_6,c_167])).

tff(c_188,plain,(
    ! [B_36,A_35] : r1_tarski(k3_xboole_0(B_36,A_35),A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_179])).

tff(c_457,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k2_relat_1(A_78),k2_relat_1(B_79))
      | ~ r1_tarski(A_78,B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_389,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k2_relat_1(A_73),k2_relat_1(B_74))
      | ~ r1_tarski(A_73,B_74)
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_212,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(A_50,k3_xboole_0(B_51,C_52))
      | ~ r1_tarski(A_50,C_52)
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_229,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_212,c_28])).

tff(c_354,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_392,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_389,c_354])).

tff(c_400,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_178,c_392])).

tff(c_405,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_250,c_400])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_405])).

tff(c_413,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_460,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_457,c_413])).

tff(c_468,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_188,c_460])).

tff(c_473,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_250,c_468])).

tff(c_480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.28  
% 2.18/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.28  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.18/1.28  
% 2.18/1.28  %Foreground sorts:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Background operators:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Foreground operators:
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.18/1.28  
% 2.18/1.30  tff(f_77, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 2.18/1.30  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.18/1.30  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.18/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.18/1.30  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.18/1.30  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.18/1.30  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.18/1.30  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.18/1.30  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.18/1.30  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.18/1.30  tff(c_12, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.30  tff(c_69, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.18/1.30  tff(c_98, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(B_36, A_35))), inference(superposition, [status(thm), theory('equality')], [c_12, c_69])).
% 2.18/1.30  tff(c_16, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.18/1.30  tff(c_104, plain, (![B_36, A_35]: (k3_xboole_0(B_36, A_35)=k3_xboole_0(A_35, B_36))), inference(superposition, [status(thm), theory('equality')], [c_98, c_16])).
% 2.18/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.30  tff(c_167, plain, (![A_43, B_44, C_45]: (r1_tarski(A_43, B_44) | ~r1_tarski(A_43, k3_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.30  tff(c_178, plain, (![B_44, C_45]: (r1_tarski(k3_xboole_0(B_44, C_45), B_44))), inference(resolution, [status(thm)], [c_6, c_167])).
% 2.18/1.30  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.30  tff(c_162, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.30  tff(c_230, plain, (![A_53, B_54]: (v1_relat_1(A_53) | ~v1_relat_1(B_54) | ~r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_20, c_162])).
% 2.18/1.30  tff(c_247, plain, (![B_55, C_56]: (v1_relat_1(k3_xboole_0(B_55, C_56)) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_178, c_230])).
% 2.18/1.30  tff(c_250, plain, (![B_36, A_35]: (v1_relat_1(k3_xboole_0(B_36, A_35)) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_104, c_247])).
% 2.18/1.30  tff(c_179, plain, (![B_46, C_47]: (r1_tarski(k3_xboole_0(B_46, C_47), B_46))), inference(resolution, [status(thm)], [c_6, c_167])).
% 2.18/1.30  tff(c_188, plain, (![B_36, A_35]: (r1_tarski(k3_xboole_0(B_36, A_35), A_35))), inference(superposition, [status(thm), theory('equality')], [c_104, c_179])).
% 2.18/1.30  tff(c_457, plain, (![A_78, B_79]: (r1_tarski(k2_relat_1(A_78), k2_relat_1(B_79)) | ~r1_tarski(A_78, B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.30  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.18/1.30  tff(c_389, plain, (![A_73, B_74]: (r1_tarski(k2_relat_1(A_73), k2_relat_1(B_74)) | ~r1_tarski(A_73, B_74) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.30  tff(c_212, plain, (![A_50, B_51, C_52]: (r1_tarski(A_50, k3_xboole_0(B_51, C_52)) | ~r1_tarski(A_50, C_52) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.30  tff(c_28, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.18/1.30  tff(c_229, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_212, c_28])).
% 2.18/1.30  tff(c_354, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_229])).
% 2.18/1.30  tff(c_392, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_389, c_354])).
% 2.18/1.30  tff(c_400, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_178, c_392])).
% 2.18/1.30  tff(c_405, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_250, c_400])).
% 2.18/1.30  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_405])).
% 2.18/1.30  tff(c_413, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_229])).
% 2.18/1.30  tff(c_460, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_457, c_413])).
% 2.18/1.30  tff(c_468, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_188, c_460])).
% 2.18/1.30  tff(c_473, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_250, c_468])).
% 2.18/1.30  tff(c_480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_473])).
% 2.18/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.30  
% 2.18/1.30  Inference rules
% 2.18/1.30  ----------------------
% 2.18/1.30  #Ref     : 0
% 2.18/1.30  #Sup     : 104
% 2.18/1.30  #Fact    : 0
% 2.18/1.30  #Define  : 0
% 2.18/1.30  #Split   : 2
% 2.18/1.30  #Chain   : 0
% 2.18/1.30  #Close   : 0
% 2.18/1.30  
% 2.18/1.30  Ordering : KBO
% 2.18/1.30  
% 2.18/1.30  Simplification rules
% 2.18/1.30  ----------------------
% 2.18/1.30  #Subsume      : 7
% 2.18/1.30  #Demod        : 32
% 2.18/1.30  #Tautology    : 51
% 2.18/1.30  #SimpNegUnit  : 0
% 2.18/1.30  #BackRed      : 0
% 2.18/1.30  
% 2.18/1.30  #Partial instantiations: 0
% 2.18/1.30  #Strategies tried      : 1
% 2.18/1.30  
% 2.18/1.30  Timing (in seconds)
% 2.18/1.30  ----------------------
% 2.18/1.30  Preprocessing        : 0.29
% 2.18/1.30  Parsing              : 0.15
% 2.18/1.30  CNF conversion       : 0.02
% 2.18/1.30  Main loop            : 0.24
% 2.18/1.30  Inferencing          : 0.08
% 2.18/1.30  Reduction            : 0.08
% 2.18/1.30  Demodulation         : 0.07
% 2.18/1.30  BG Simplification    : 0.01
% 2.18/1.30  Subsumption          : 0.05
% 2.18/1.30  Abstraction          : 0.01
% 2.18/1.30  MUC search           : 0.00
% 2.18/1.30  Cooper               : 0.00
% 2.18/1.30  Total                : 0.57
% 2.18/1.30  Index Insertion      : 0.00
% 2.18/1.30  Index Deletion       : 0.00
% 2.18/1.30  Index Matching       : 0.00
% 2.18/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
