%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:45 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 111 expanded)
%              Number of leaves         :   34 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 175 expanded)
%              Number of equality atoms :    5 (  20 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_18,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_xboole_0(A_16,B_17),k4_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k2_xboole_0(k3_xboole_0(A_10,B_11),k3_xboole_0(A_10,C_12)) = k3_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] : r1_tarski(k2_xboole_0(k3_xboole_0(A_13,B_14),k3_xboole_0(A_13,C_15)),k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_140,plain,(
    ! [A_101,B_102,C_103] : r1_tarski(k3_xboole_0(A_101,k2_xboole_0(B_102,C_103)),k2_xboole_0(B_102,C_103)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_148,plain,(
    ! [A_101,A_16,B_17] : r1_tarski(k3_xboole_0(A_101,A_16),k2_xboole_0(k3_xboole_0(A_16,B_17),k4_xboole_0(A_16,B_17))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_140])).

tff(c_169,plain,(
    ! [A_107,A_108] : r1_tarski(k3_xboole_0(A_107,A_108),A_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_148])).

tff(c_38,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(A_49,k1_zfmisc_1(B_50))
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_88,plain,(
    ! [B_86,A_87] :
      ( v1_relat_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87))
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_92,plain,(
    ! [A_49,B_50] :
      ( v1_relat_1(A_49)
      | ~ v1_relat_1(B_50)
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_38,c_88])).

tff(c_176,plain,(
    ! [A_107,A_108] :
      ( v1_relat_1(k3_xboole_0(A_107,A_108))
      | ~ v1_relat_1(A_108) ) ),
    inference(resolution,[status(thm)],[c_169,c_92])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [A_101,A_16] : r1_tarski(k3_xboole_0(A_101,A_16),A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_148])).

tff(c_2361,plain,(
    ! [A_236,C_237,B_238,D_239] :
      ( r1_tarski(k5_relat_1(A_236,C_237),k5_relat_1(B_238,D_239))
      | ~ r1_tarski(C_237,D_239)
      | ~ r1_tarski(A_236,B_238)
      | ~ v1_relat_1(D_239)
      | ~ v1_relat_1(C_237)
      | ~ v1_relat_1(B_238)
      | ~ v1_relat_1(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1020,plain,(
    ! [A_171,C_172,B_173,D_174] :
      ( r1_tarski(k5_relat_1(A_171,C_172),k5_relat_1(B_173,D_174))
      | ~ r1_tarski(C_172,D_174)
      | ~ r1_tarski(A_171,B_173)
      | ~ v1_relat_1(D_174)
      | ~ v1_relat_1(C_172)
      | ~ v1_relat_1(B_173)
      | ~ v1_relat_1(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_156,plain,(
    ! [A_104,B_105,C_106] :
      ( r1_tarski(A_104,k3_xboole_0(B_105,C_106))
      | ~ r1_tarski(A_104,C_106)
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_167,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_156,c_44])).

tff(c_268,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_1026,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1020,c_268])).

tff(c_1038,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_6,c_10,c_1026])).

tff(c_1044,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_1038])).

tff(c_1051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1044])).

tff(c_1052,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_2370,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2361,c_1052])).

tff(c_2385,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_6,c_154,c_2370])).

tff(c_2391,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_2385])).

tff(c_2398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2391])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.54  
% 3.75/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.54  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.75/1.54  
% 3.75/1.54  %Foreground sorts:
% 3.75/1.54  
% 3.75/1.54  
% 3.75/1.54  %Background operators:
% 3.75/1.54  
% 3.75/1.54  
% 3.75/1.54  %Foreground operators:
% 3.75/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.75/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.75/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.75/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.75/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.75/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.75/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.75/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.75/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.75/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.75/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.75/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.75/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.75/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.75/1.54  
% 3.75/1.56  tff(f_102, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 3.75/1.56  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.75/1.56  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 3.75/1.56  tff(f_45, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 3.75/1.56  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.75/1.56  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.75/1.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.75/1.56  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relat_1)).
% 3.75/1.56  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.75/1.56  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.75/1.56  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.75/1.56  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(k3_xboole_0(A_16, B_17), k4_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.75/1.56  tff(c_14, plain, (![A_10, B_11, C_12]: (k2_xboole_0(k3_xboole_0(A_10, B_11), k3_xboole_0(A_10, C_12))=k3_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.75/1.56  tff(c_16, plain, (![A_13, B_14, C_15]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_13, B_14), k3_xboole_0(A_13, C_15)), k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.75/1.56  tff(c_140, plain, (![A_101, B_102, C_103]: (r1_tarski(k3_xboole_0(A_101, k2_xboole_0(B_102, C_103)), k2_xboole_0(B_102, C_103)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.75/1.56  tff(c_148, plain, (![A_101, A_16, B_17]: (r1_tarski(k3_xboole_0(A_101, A_16), k2_xboole_0(k3_xboole_0(A_16, B_17), k4_xboole_0(A_16, B_17))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_140])).
% 3.75/1.56  tff(c_169, plain, (![A_107, A_108]: (r1_tarski(k3_xboole_0(A_107, A_108), A_108))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_148])).
% 3.75/1.56  tff(c_38, plain, (![A_49, B_50]: (m1_subset_1(A_49, k1_zfmisc_1(B_50)) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.75/1.56  tff(c_88, plain, (![B_86, A_87]: (v1_relat_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.75/1.56  tff(c_92, plain, (![A_49, B_50]: (v1_relat_1(A_49) | ~v1_relat_1(B_50) | ~r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_38, c_88])).
% 3.75/1.56  tff(c_176, plain, (![A_107, A_108]: (v1_relat_1(k3_xboole_0(A_107, A_108)) | ~v1_relat_1(A_108))), inference(resolution, [status(thm)], [c_169, c_92])).
% 3.75/1.56  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.75/1.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.75/1.56  tff(c_154, plain, (![A_101, A_16]: (r1_tarski(k3_xboole_0(A_101, A_16), A_16))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_148])).
% 3.75/1.56  tff(c_2361, plain, (![A_236, C_237, B_238, D_239]: (r1_tarski(k5_relat_1(A_236, C_237), k5_relat_1(B_238, D_239)) | ~r1_tarski(C_237, D_239) | ~r1_tarski(A_236, B_238) | ~v1_relat_1(D_239) | ~v1_relat_1(C_237) | ~v1_relat_1(B_238) | ~v1_relat_1(A_236))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.75/1.56  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.75/1.56  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.75/1.56  tff(c_1020, plain, (![A_171, C_172, B_173, D_174]: (r1_tarski(k5_relat_1(A_171, C_172), k5_relat_1(B_173, D_174)) | ~r1_tarski(C_172, D_174) | ~r1_tarski(A_171, B_173) | ~v1_relat_1(D_174) | ~v1_relat_1(C_172) | ~v1_relat_1(B_173) | ~v1_relat_1(A_171))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.75/1.56  tff(c_156, plain, (![A_104, B_105, C_106]: (r1_tarski(A_104, k3_xboole_0(B_105, C_106)) | ~r1_tarski(A_104, C_106) | ~r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.75/1.56  tff(c_44, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.75/1.56  tff(c_167, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_156, c_44])).
% 3.75/1.56  tff(c_268, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_167])).
% 3.75/1.56  tff(c_1026, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1020, c_268])).
% 3.75/1.56  tff(c_1038, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_6, c_10, c_1026])).
% 3.75/1.56  tff(c_1044, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_176, c_1038])).
% 3.75/1.56  tff(c_1051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1044])).
% 3.75/1.56  tff(c_1052, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_167])).
% 3.75/1.56  tff(c_2370, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2361, c_1052])).
% 3.75/1.56  tff(c_2385, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_6, c_154, c_2370])).
% 3.75/1.56  tff(c_2391, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_176, c_2385])).
% 3.75/1.56  tff(c_2398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2391])).
% 3.75/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.56  
% 3.75/1.56  Inference rules
% 3.75/1.56  ----------------------
% 3.75/1.56  #Ref     : 0
% 3.75/1.56  #Sup     : 602
% 3.75/1.56  #Fact    : 0
% 3.75/1.56  #Define  : 0
% 3.75/1.56  #Split   : 3
% 3.75/1.56  #Chain   : 0
% 3.75/1.56  #Close   : 0
% 3.75/1.56  
% 3.75/1.56  Ordering : KBO
% 3.75/1.56  
% 3.75/1.56  Simplification rules
% 3.75/1.56  ----------------------
% 3.75/1.56  #Subsume      : 47
% 3.75/1.56  #Demod        : 382
% 3.75/1.56  #Tautology    : 285
% 3.75/1.56  #SimpNegUnit  : 0
% 3.75/1.56  #BackRed      : 0
% 3.75/1.56  
% 3.75/1.56  #Partial instantiations: 0
% 3.75/1.56  #Strategies tried      : 1
% 3.75/1.56  
% 3.75/1.56  Timing (in seconds)
% 3.75/1.56  ----------------------
% 3.75/1.56  Preprocessing        : 0.31
% 3.75/1.56  Parsing              : 0.17
% 3.75/1.56  CNF conversion       : 0.02
% 3.75/1.56  Main loop            : 0.55
% 3.75/1.56  Inferencing          : 0.20
% 3.75/1.56  Reduction            : 0.20
% 3.75/1.56  Demodulation         : 0.16
% 3.75/1.56  BG Simplification    : 0.03
% 3.75/1.56  Subsumption          : 0.09
% 3.75/1.56  Abstraction          : 0.03
% 3.75/1.56  MUC search           : 0.00
% 3.75/1.56  Cooper               : 0.00
% 3.75/1.56  Total                : 0.89
% 3.75/1.56  Index Insertion      : 0.00
% 3.75/1.56  Index Deletion       : 0.00
% 3.75/1.56  Index Matching       : 0.00
% 3.75/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
