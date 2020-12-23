%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:39 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   55 (  96 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 135 expanded)
%              Number of equality atoms :    4 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
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

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k3_xboole_0(A_6,B_7),k3_xboole_0(A_6,C_8)) = k3_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : r1_tarski(k2_xboole_0(k3_xboole_0(A_9,B_10),k3_xboole_0(A_9,C_11)),k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [A_49,B_50,C_51] : r1_tarski(k3_xboole_0(A_49,k2_xboole_0(B_50,C_51)),k2_xboole_0(B_50,C_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_92,plain,(
    ! [A_49,A_12,B_13] : r1_tarski(k3_xboole_0(A_49,A_12),k2_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_86])).

tff(c_100,plain,(
    ! [A_52,A_53] : r1_tarski(k3_xboole_0(A_52,A_53),A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_79,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(A_20)
      | ~ v1_relat_1(B_21)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_104,plain,(
    ! [A_52,A_53] :
      ( v1_relat_1(k3_xboole_0(A_52,A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(resolution,[status(thm)],[c_100,c_79])).

tff(c_97,plain,(
    ! [A_49,A_12] : r1_tarski(k3_xboole_0(A_49,A_12),A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_163,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k3_relat_1(A_67),k3_relat_1(B_68))
      | ~ r1_tarski(A_67,B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_126,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k3_relat_1(A_62),k3_relat_1(B_63))
      | ~ r1_tarski(A_62,B_63)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_105,plain,(
    ! [A_54,B_55,C_56] :
      ( r1_tarski(A_54,k3_xboole_0(B_55,C_56))
      | ~ r1_tarski(A_54,C_56)
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_113,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_105,c_26])).

tff(c_116,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_129,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_126,c_116])).

tff(c_135,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2,c_129])).

tff(c_139,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_135])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_139])).

tff(c_147,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_166,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_163,c_147])).

tff(c_172,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_97,c_166])).

tff(c_176,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_172])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:48:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.26  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 1.99/1.26  
% 1.99/1.26  %Foreground sorts:
% 1.99/1.26  
% 1.99/1.26  
% 1.99/1.26  %Background operators:
% 1.99/1.26  
% 1.99/1.26  
% 1.99/1.26  %Foreground operators:
% 1.99/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.26  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.99/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.99/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.99/1.26  
% 1.99/1.27  tff(f_73, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 1.99/1.27  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.99/1.27  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 1.99/1.27  tff(f_37, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 1.99/1.27  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.99/1.27  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.99/1.27  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 1.99/1.27  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.99/1.27  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.99/1.27  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.99/1.27  tff(c_10, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.27  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k3_xboole_0(A_6, B_7), k3_xboole_0(A_6, C_8))=k3_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.27  tff(c_8, plain, (![A_9, B_10, C_11]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_9, B_10), k3_xboole_0(A_9, C_11)), k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.27  tff(c_86, plain, (![A_49, B_50, C_51]: (r1_tarski(k3_xboole_0(A_49, k2_xboole_0(B_50, C_51)), k2_xboole_0(B_50, C_51)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 1.99/1.27  tff(c_92, plain, (![A_49, A_12, B_13]: (r1_tarski(k3_xboole_0(A_49, A_12), k2_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_86])).
% 1.99/1.27  tff(c_100, plain, (![A_52, A_53]: (r1_tarski(k3_xboole_0(A_52, A_53), A_53))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_92])).
% 1.99/1.27  tff(c_20, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.99/1.27  tff(c_75, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.27  tff(c_79, plain, (![A_20, B_21]: (v1_relat_1(A_20) | ~v1_relat_1(B_21) | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_20, c_75])).
% 1.99/1.27  tff(c_104, plain, (![A_52, A_53]: (v1_relat_1(k3_xboole_0(A_52, A_53)) | ~v1_relat_1(A_53))), inference(resolution, [status(thm)], [c_100, c_79])).
% 1.99/1.27  tff(c_97, plain, (![A_49, A_12]: (r1_tarski(k3_xboole_0(A_49, A_12), A_12))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_92])).
% 1.99/1.27  tff(c_163, plain, (![A_67, B_68]: (r1_tarski(k3_relat_1(A_67), k3_relat_1(B_68)) | ~r1_tarski(A_67, B_68) | ~v1_relat_1(B_68) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.27  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.99/1.27  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.27  tff(c_126, plain, (![A_62, B_63]: (r1_tarski(k3_relat_1(A_62), k3_relat_1(B_63)) | ~r1_tarski(A_62, B_63) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.27  tff(c_105, plain, (![A_54, B_55, C_56]: (r1_tarski(A_54, k3_xboole_0(B_55, C_56)) | ~r1_tarski(A_54, C_56) | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.27  tff(c_26, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.99/1.27  tff(c_113, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_105, c_26])).
% 1.99/1.27  tff(c_116, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_113])).
% 1.99/1.27  tff(c_129, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_126, c_116])).
% 1.99/1.27  tff(c_135, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2, c_129])).
% 1.99/1.27  tff(c_139, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_104, c_135])).
% 1.99/1.27  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_139])).
% 1.99/1.27  tff(c_147, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_113])).
% 1.99/1.27  tff(c_166, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_163, c_147])).
% 1.99/1.27  tff(c_172, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_97, c_166])).
% 1.99/1.27  tff(c_176, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_104, c_172])).
% 1.99/1.27  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_176])).
% 1.99/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.27  
% 1.99/1.27  Inference rules
% 1.99/1.27  ----------------------
% 1.99/1.27  #Ref     : 0
% 1.99/1.27  #Sup     : 30
% 1.99/1.27  #Fact    : 0
% 1.99/1.27  #Define  : 0
% 1.99/1.27  #Split   : 2
% 1.99/1.27  #Chain   : 0
% 1.99/1.27  #Close   : 0
% 1.99/1.27  
% 1.99/1.27  Ordering : KBO
% 1.99/1.27  
% 1.99/1.27  Simplification rules
% 1.99/1.27  ----------------------
% 1.99/1.27  #Subsume      : 1
% 1.99/1.27  #Demod        : 11
% 1.99/1.27  #Tautology    : 15
% 1.99/1.27  #SimpNegUnit  : 0
% 1.99/1.27  #BackRed      : 0
% 1.99/1.27  
% 1.99/1.27  #Partial instantiations: 0
% 1.99/1.27  #Strategies tried      : 1
% 1.99/1.27  
% 1.99/1.27  Timing (in seconds)
% 1.99/1.27  ----------------------
% 1.99/1.27  Preprocessing        : 0.30
% 1.99/1.27  Parsing              : 0.17
% 1.99/1.27  CNF conversion       : 0.02
% 1.99/1.27  Main loop            : 0.15
% 1.99/1.27  Inferencing          : 0.06
% 1.99/1.27  Reduction            : 0.04
% 1.99/1.27  Demodulation         : 0.03
% 1.99/1.27  BG Simplification    : 0.01
% 1.99/1.27  Subsumption          : 0.03
% 1.99/1.27  Abstraction          : 0.01
% 1.99/1.27  MUC search           : 0.00
% 1.99/1.27  Cooper               : 0.00
% 1.99/1.27  Total                : 0.48
% 1.99/1.27  Index Insertion      : 0.00
% 1.99/1.27  Index Deletion       : 0.00
% 1.99/1.27  Index Matching       : 0.00
% 1.99/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
