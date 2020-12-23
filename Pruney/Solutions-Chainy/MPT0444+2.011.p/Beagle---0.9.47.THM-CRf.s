%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:22 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   56 (  88 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 150 expanded)
%              Number of equality atoms :    6 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_46,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_setfam_1(B_19),A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_81,plain,(
    ! [A_45,B_46] :
      ( v1_relat_1(A_45)
      | ~ v1_relat_1(B_46)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_30,c_76])).

tff(c_91,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(k1_setfam_1(B_49))
      | ~ v1_relat_1(A_50)
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_32,c_81])).

tff(c_93,plain,(
    ! [A_6,D_11] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_6,D_11)))
      | ~ v1_relat_1(D_11) ) ),
    inference(resolution,[status(thm)],[c_8,c_91])).

tff(c_97,plain,(
    ! [A_6,D_11] :
      ( v1_relat_1(k3_xboole_0(A_6,D_11))
      | ~ v1_relat_1(D_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_93])).

tff(c_55,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_112,plain,(
    ! [A_56,B_57,A_58] :
      ( r1_tarski(k3_xboole_0(A_56,B_57),A_58)
      | ~ r2_hidden(A_58,k2_tarski(A_56,B_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_32])).

tff(c_119,plain,(
    ! [A_6,D_11] : r1_tarski(k3_xboole_0(A_6,D_11),D_11) ),
    inference(resolution,[status(thm)],[c_8,c_112])).

tff(c_36,plain,(
    ! [A_23,B_25] :
      ( r1_tarski(k2_relat_1(A_23),k2_relat_1(B_25))
      | ~ r1_tarski(A_23,B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_127,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(A_61,k3_xboole_0(B_62,C_63))
      | ~ r1_tarski(A_61,C_63)
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_135,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_127,c_40])).

tff(c_156,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_159,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_156])).

tff(c_162,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2,c_159])).

tff(c_165,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_162])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_165])).

tff(c_173,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_177,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_173])).

tff(c_180,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_119,c_177])).

tff(c_183,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_180])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:32:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.22  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.91/1.22  
% 1.91/1.22  %Foreground sorts:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Background operators:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Foreground operators:
% 1.91/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.91/1.22  
% 1.91/1.23  tff(f_80, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 1.91/1.23  tff(f_46, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.91/1.23  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.91/1.23  tff(f_54, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.91/1.23  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.91/1.23  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.91/1.23  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.91/1.23  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.91/1.23  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.91/1.23  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.23  tff(c_26, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.23  tff(c_8, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.91/1.23  tff(c_32, plain, (![B_19, A_18]: (r1_tarski(k1_setfam_1(B_19), A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.91/1.23  tff(c_30, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.23  tff(c_76, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.91/1.23  tff(c_81, plain, (![A_45, B_46]: (v1_relat_1(A_45) | ~v1_relat_1(B_46) | ~r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_30, c_76])).
% 1.91/1.23  tff(c_91, plain, (![B_49, A_50]: (v1_relat_1(k1_setfam_1(B_49)) | ~v1_relat_1(A_50) | ~r2_hidden(A_50, B_49))), inference(resolution, [status(thm)], [c_32, c_81])).
% 1.91/1.23  tff(c_93, plain, (![A_6, D_11]: (v1_relat_1(k1_setfam_1(k2_tarski(A_6, D_11))) | ~v1_relat_1(D_11))), inference(resolution, [status(thm)], [c_8, c_91])).
% 1.91/1.23  tff(c_97, plain, (![A_6, D_11]: (v1_relat_1(k3_xboole_0(A_6, D_11)) | ~v1_relat_1(D_11))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_93])).
% 1.91/1.23  tff(c_55, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.23  tff(c_112, plain, (![A_56, B_57, A_58]: (r1_tarski(k3_xboole_0(A_56, B_57), A_58) | ~r2_hidden(A_58, k2_tarski(A_56, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_32])).
% 1.91/1.23  tff(c_119, plain, (![A_6, D_11]: (r1_tarski(k3_xboole_0(A_6, D_11), D_11))), inference(resolution, [status(thm)], [c_8, c_112])).
% 1.91/1.23  tff(c_36, plain, (![A_23, B_25]: (r1_tarski(k2_relat_1(A_23), k2_relat_1(B_25)) | ~r1_tarski(A_23, B_25) | ~v1_relat_1(B_25) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.91/1.23  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.23  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.23  tff(c_127, plain, (![A_61, B_62, C_63]: (r1_tarski(A_61, k3_xboole_0(B_62, C_63)) | ~r1_tarski(A_61, C_63) | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.23  tff(c_40, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.91/1.23  tff(c_135, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_127, c_40])).
% 1.91/1.23  tff(c_156, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_135])).
% 1.91/1.23  tff(c_159, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_156])).
% 1.91/1.23  tff(c_162, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2, c_159])).
% 1.91/1.23  tff(c_165, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_97, c_162])).
% 1.91/1.23  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_165])).
% 1.91/1.23  tff(c_173, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_135])).
% 1.91/1.23  tff(c_177, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_173])).
% 1.91/1.23  tff(c_180, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_119, c_177])).
% 1.91/1.23  tff(c_183, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_97, c_180])).
% 1.91/1.23  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_183])).
% 1.91/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.23  
% 1.91/1.23  Inference rules
% 1.91/1.23  ----------------------
% 1.91/1.23  #Ref     : 0
% 1.91/1.23  #Sup     : 28
% 1.91/1.23  #Fact    : 0
% 1.91/1.23  #Define  : 0
% 1.91/1.24  #Split   : 1
% 1.91/1.24  #Chain   : 0
% 1.91/1.24  #Close   : 0
% 1.91/1.24  
% 1.91/1.24  Ordering : KBO
% 1.91/1.24  
% 1.91/1.24  Simplification rules
% 1.91/1.24  ----------------------
% 1.91/1.24  #Subsume      : 4
% 1.91/1.24  #Demod        : 9
% 1.91/1.24  #Tautology    : 8
% 1.91/1.24  #SimpNegUnit  : 0
% 1.91/1.24  #BackRed      : 0
% 1.91/1.24  
% 1.91/1.24  #Partial instantiations: 0
% 1.91/1.24  #Strategies tried      : 1
% 1.91/1.24  
% 1.91/1.24  Timing (in seconds)
% 1.91/1.24  ----------------------
% 1.91/1.24  Preprocessing        : 0.31
% 1.91/1.24  Parsing              : 0.16
% 1.91/1.24  CNF conversion       : 0.02
% 1.91/1.24  Main loop            : 0.17
% 1.91/1.24  Inferencing          : 0.06
% 1.91/1.24  Reduction            : 0.05
% 1.91/1.24  Demodulation         : 0.04
% 1.91/1.24  BG Simplification    : 0.01
% 1.91/1.24  Subsumption          : 0.03
% 1.91/1.24  Abstraction          : 0.01
% 1.91/1.24  MUC search           : 0.00
% 1.91/1.24  Cooper               : 0.00
% 1.91/1.24  Total                : 0.51
% 1.91/1.24  Index Insertion      : 0.00
% 1.91/1.24  Index Deletion       : 0.00
% 1.91/1.24  Index Matching       : 0.00
% 1.91/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
