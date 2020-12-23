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
% DateTime   : Thu Dec  3 09:58:38 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   56 (  88 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 148 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_48,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_setfam_1(B_22),A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    ! [A_48,B_49] :
      ( v1_relat_1(A_48)
      | ~ v1_relat_1(B_49)
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_32,c_76])).

tff(c_91,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(k1_setfam_1(B_52))
      | ~ v1_relat_1(A_53)
      | ~ r2_hidden(A_53,B_52) ) ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_93,plain,(
    ! [A_6,D_11] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_6,D_11)))
      | ~ v1_relat_1(D_11) ) ),
    inference(resolution,[status(thm)],[c_8,c_91])).

tff(c_97,plain,(
    ! [A_6,D_11] :
      ( v1_relat_1(k3_xboole_0(A_6,D_11))
      | ~ v1_relat_1(D_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_93])).

tff(c_63,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(k1_setfam_1(B_42),A_43)
      | ~ r2_hidden(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_121,plain,(
    ! [A_62,B_63,A_64] :
      ( r1_tarski(k3_xboole_0(A_62,B_63),A_64)
      | ~ r2_hidden(A_64,k2_tarski(A_62,B_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_63])).

tff(c_128,plain,(
    ! [A_6,D_11] : r1_tarski(k3_xboole_0(A_6,D_11),D_11) ),
    inference(resolution,[status(thm)],[c_8,c_121])).

tff(c_38,plain,(
    ! [A_26,B_28] :
      ( r1_tarski(k3_relat_1(A_26),k3_relat_1(B_28))
      | ~ r1_tarski(A_26,B_28)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_131,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(A_65,k3_xboole_0(B_66,C_67))
      | ~ r1_tarski(A_65,C_67)
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_139,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_131,c_40])).

tff(c_158,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_162,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_158])).

tff(c_165,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2,c_162])).

tff(c_168,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_165])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_168])).

tff(c_176,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_180,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_176])).

tff(c_183,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_128,c_180])).

tff(c_190,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_183])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.19  
% 1.99/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.99/1.20  
% 1.99/1.20  %Foreground sorts:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Background operators:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Foreground operators:
% 1.99/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.20  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.99/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.99/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.99/1.20  
% 2.06/1.21  tff(f_80, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 2.06/1.21  tff(f_48, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.06/1.21  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.06/1.21  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.06/1.21  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.06/1.21  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.06/1.21  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.06/1.21  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.06/1.21  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.06/1.21  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.06/1.21  tff(c_28, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.06/1.21  tff(c_8, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.21  tff(c_34, plain, (![B_22, A_21]: (r1_tarski(k1_setfam_1(B_22), A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.21  tff(c_32, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.06/1.21  tff(c_76, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.06/1.21  tff(c_81, plain, (![A_48, B_49]: (v1_relat_1(A_48) | ~v1_relat_1(B_49) | ~r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_32, c_76])).
% 2.06/1.21  tff(c_91, plain, (![B_52, A_53]: (v1_relat_1(k1_setfam_1(B_52)) | ~v1_relat_1(A_53) | ~r2_hidden(A_53, B_52))), inference(resolution, [status(thm)], [c_34, c_81])).
% 2.06/1.21  tff(c_93, plain, (![A_6, D_11]: (v1_relat_1(k1_setfam_1(k2_tarski(A_6, D_11))) | ~v1_relat_1(D_11))), inference(resolution, [status(thm)], [c_8, c_91])).
% 2.06/1.21  tff(c_97, plain, (![A_6, D_11]: (v1_relat_1(k3_xboole_0(A_6, D_11)) | ~v1_relat_1(D_11))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_93])).
% 2.06/1.21  tff(c_63, plain, (![B_42, A_43]: (r1_tarski(k1_setfam_1(B_42), A_43) | ~r2_hidden(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.21  tff(c_121, plain, (![A_62, B_63, A_64]: (r1_tarski(k3_xboole_0(A_62, B_63), A_64) | ~r2_hidden(A_64, k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_63])).
% 2.06/1.21  tff(c_128, plain, (![A_6, D_11]: (r1_tarski(k3_xboole_0(A_6, D_11), D_11))), inference(resolution, [status(thm)], [c_8, c_121])).
% 2.06/1.21  tff(c_38, plain, (![A_26, B_28]: (r1_tarski(k3_relat_1(A_26), k3_relat_1(B_28)) | ~r1_tarski(A_26, B_28) | ~v1_relat_1(B_28) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.06/1.21  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.06/1.21  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.21  tff(c_131, plain, (![A_65, B_66, C_67]: (r1_tarski(A_65, k3_xboole_0(B_66, C_67)) | ~r1_tarski(A_65, C_67) | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.21  tff(c_40, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.06/1.21  tff(c_139, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_131, c_40])).
% 2.06/1.21  tff(c_158, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_139])).
% 2.06/1.21  tff(c_162, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_158])).
% 2.06/1.21  tff(c_165, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2, c_162])).
% 2.06/1.21  tff(c_168, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_97, c_165])).
% 2.06/1.21  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_168])).
% 2.06/1.21  tff(c_176, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_139])).
% 2.06/1.21  tff(c_180, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_176])).
% 2.06/1.21  tff(c_183, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_128, c_180])).
% 2.06/1.21  tff(c_190, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_97, c_183])).
% 2.06/1.21  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_190])).
% 2.06/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.21  
% 2.06/1.21  Inference rules
% 2.06/1.21  ----------------------
% 2.06/1.21  #Ref     : 0
% 2.06/1.21  #Sup     : 30
% 2.06/1.21  #Fact    : 0
% 2.06/1.21  #Define  : 0
% 2.06/1.21  #Split   : 1
% 2.06/1.21  #Chain   : 0
% 2.06/1.21  #Close   : 0
% 2.06/1.21  
% 2.06/1.21  Ordering : KBO
% 2.06/1.21  
% 2.06/1.21  Simplification rules
% 2.06/1.21  ----------------------
% 2.06/1.21  #Subsume      : 4
% 2.06/1.21  #Demod        : 9
% 2.06/1.21  #Tautology    : 10
% 2.06/1.21  #SimpNegUnit  : 0
% 2.06/1.21  #BackRed      : 0
% 2.06/1.21  
% 2.06/1.21  #Partial instantiations: 0
% 2.06/1.21  #Strategies tried      : 1
% 2.06/1.21  
% 2.06/1.21  Timing (in seconds)
% 2.06/1.21  ----------------------
% 2.06/1.21  Preprocessing        : 0.30
% 2.06/1.21  Parsing              : 0.16
% 2.06/1.21  CNF conversion       : 0.02
% 2.06/1.21  Main loop            : 0.16
% 2.06/1.21  Inferencing          : 0.06
% 2.06/1.21  Reduction            : 0.05
% 2.06/1.21  Demodulation         : 0.03
% 2.06/1.21  BG Simplification    : 0.01
% 2.06/1.21  Subsumption          : 0.03
% 2.06/1.21  Abstraction          : 0.01
% 2.06/1.21  MUC search           : 0.00
% 2.06/1.21  Cooper               : 0.00
% 2.06/1.21  Total                : 0.49
% 2.06/1.21  Index Insertion      : 0.00
% 2.06/1.21  Index Deletion       : 0.00
% 2.06/1.21  Index Matching       : 0.00
% 2.06/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
