%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:43 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   54 (  91 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 161 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ! [D] :
                  ( v1_relat_1(D)
                 => ( ( r1_tarski(A,B)
                      & r1_tarski(C,D) )
                   => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_129,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_143,plain,(
    ! [A_72,B_73] :
      ( v1_relat_1(A_72)
      | ~ v1_relat_1(B_73)
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_26,c_129])).

tff(c_154,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k3_xboole_0(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_143])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    ! [B_53,A_54] : k3_xboole_0(B_53,A_54) = k3_xboole_0(A_54,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    ! [B_53,A_54] : r1_tarski(k3_xboole_0(B_53,A_54),A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_10])).

tff(c_1357,plain,(
    ! [A_126,C_127,B_128,D_129] :
      ( r1_tarski(k5_relat_1(A_126,C_127),k5_relat_1(B_128,D_129))
      | ~ r1_tarski(C_127,D_129)
      | ~ r1_tarski(A_126,B_128)
      | ~ v1_relat_1(D_129)
      | ~ v1_relat_1(C_127)
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_891,plain,(
    ! [A_109,C_110,B_111,D_112] :
      ( r1_tarski(k5_relat_1(A_109,C_110),k5_relat_1(B_111,D_112))
      | ~ r1_tarski(C_110,D_112)
      | ~ r1_tarski(A_109,B_111)
      | ~ v1_relat_1(D_112)
      | ~ v1_relat_1(C_110)
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_170,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_tarski(A_78,k3_xboole_0(B_79,C_80))
      | ~ r1_tarski(A_78,C_80)
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_32])).

tff(c_187,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_170,c_40])).

tff(c_467,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_894,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_891,c_467])).

tff(c_905,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_8,c_10,c_894])).

tff(c_911,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_154,c_905])).

tff(c_918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_911])).

tff(c_919,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_1360,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1357,c_919])).

tff(c_1371,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_8,c_58,c_1360])).

tff(c_1377,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_154,c_1371])).

tff(c_1384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:27:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.49  
% 3.05/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.49  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.05/1.49  
% 3.05/1.49  %Foreground sorts:
% 3.05/1.49  
% 3.05/1.49  
% 3.05/1.49  %Background operators:
% 3.05/1.49  
% 3.05/1.49  
% 3.05/1.49  %Foreground operators:
% 3.05/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.05/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.05/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.05/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.05/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.05/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.05/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.05/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.05/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.05/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.05/1.49  
% 3.26/1.50  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 3.26/1.50  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.26/1.50  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.26/1.50  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.26/1.50  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.26/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.26/1.50  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 3.26/1.50  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.26/1.50  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.26/1.50  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.50  tff(c_26, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.26/1.50  tff(c_129, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.26/1.50  tff(c_143, plain, (![A_72, B_73]: (v1_relat_1(A_72) | ~v1_relat_1(B_73) | ~r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_26, c_129])).
% 3.26/1.50  tff(c_154, plain, (![A_5, B_6]: (v1_relat_1(k3_xboole_0(A_5, B_6)) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_10, c_143])).
% 3.26/1.50  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.26/1.50  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.26/1.50  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.50  tff(c_43, plain, (![B_53, A_54]: (k3_xboole_0(B_53, A_54)=k3_xboole_0(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.50  tff(c_58, plain, (![B_53, A_54]: (r1_tarski(k3_xboole_0(B_53, A_54), A_54))), inference(superposition, [status(thm), theory('equality')], [c_43, c_10])).
% 3.26/1.50  tff(c_1357, plain, (![A_126, C_127, B_128, D_129]: (r1_tarski(k5_relat_1(A_126, C_127), k5_relat_1(B_128, D_129)) | ~r1_tarski(C_127, D_129) | ~r1_tarski(A_126, B_128) | ~v1_relat_1(D_129) | ~v1_relat_1(C_127) | ~v1_relat_1(B_128) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.50  tff(c_891, plain, (![A_109, C_110, B_111, D_112]: (r1_tarski(k5_relat_1(A_109, C_110), k5_relat_1(B_111, D_112)) | ~r1_tarski(C_110, D_112) | ~r1_tarski(A_109, B_111) | ~v1_relat_1(D_112) | ~v1_relat_1(C_110) | ~v1_relat_1(B_111) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.50  tff(c_170, plain, (![A_78, B_79, C_80]: (r1_tarski(A_78, k3_xboole_0(B_79, C_80)) | ~r1_tarski(A_78, C_80) | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.50  tff(c_32, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.26/1.50  tff(c_40, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_32])).
% 3.26/1.50  tff(c_187, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_170, c_40])).
% 3.26/1.50  tff(c_467, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_187])).
% 3.26/1.50  tff(c_894, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_891, c_467])).
% 3.26/1.50  tff(c_905, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_8, c_10, c_894])).
% 3.26/1.50  tff(c_911, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_154, c_905])).
% 3.26/1.50  tff(c_918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_911])).
% 3.26/1.50  tff(c_919, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_187])).
% 3.26/1.50  tff(c_1360, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1357, c_919])).
% 3.26/1.50  tff(c_1371, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_8, c_58, c_1360])).
% 3.26/1.50  tff(c_1377, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_154, c_1371])).
% 3.26/1.50  tff(c_1384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1377])).
% 3.26/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.50  
% 3.26/1.50  Inference rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Ref     : 0
% 3.26/1.50  #Sup     : 334
% 3.26/1.50  #Fact    : 0
% 3.26/1.50  #Define  : 0
% 3.26/1.50  #Split   : 1
% 3.26/1.50  #Chain   : 0
% 3.26/1.50  #Close   : 0
% 3.26/1.50  
% 3.26/1.50  Ordering : KBO
% 3.26/1.50  
% 3.26/1.50  Simplification rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Subsume      : 40
% 3.26/1.50  #Demod        : 312
% 3.26/1.50  #Tautology    : 206
% 3.26/1.50  #SimpNegUnit  : 0
% 3.26/1.50  #BackRed      : 0
% 3.26/1.50  
% 3.26/1.50  #Partial instantiations: 0
% 3.26/1.50  #Strategies tried      : 1
% 3.26/1.50  
% 3.26/1.51  Timing (in seconds)
% 3.26/1.51  ----------------------
% 3.26/1.51  Preprocessing        : 0.32
% 3.26/1.51  Parsing              : 0.17
% 3.26/1.51  CNF conversion       : 0.02
% 3.26/1.51  Main loop            : 0.41
% 3.26/1.51  Inferencing          : 0.13
% 3.26/1.51  Reduction            : 0.17
% 3.26/1.51  Demodulation         : 0.14
% 3.26/1.51  BG Simplification    : 0.02
% 3.26/1.51  Subsumption          : 0.06
% 3.26/1.51  Abstraction          : 0.02
% 3.26/1.51  MUC search           : 0.00
% 3.26/1.51  Cooper               : 0.00
% 3.26/1.51  Total                : 0.75
% 3.26/1.51  Index Insertion      : 0.00
% 3.26/1.51  Index Deletion       : 0.00
% 3.26/1.51  Index Matching       : 0.00
% 3.26/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
