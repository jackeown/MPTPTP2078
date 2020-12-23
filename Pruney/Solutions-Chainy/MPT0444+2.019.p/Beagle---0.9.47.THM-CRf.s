%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:23 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 103 expanded)
%              Number of leaves         :   34 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 157 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k3_xboole_0(k3_xboole_0(A_3,B_4),C_5) = k3_xboole_0(A_3,k3_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_119,plain,(
    ! [A_84,B_85,C_86] : k4_xboole_0(k3_xboole_0(A_84,B_85),C_86) = k3_xboole_0(A_84,k4_xboole_0(B_85,C_86)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_125,plain,(
    ! [A_84,B_85,C_86] : k2_xboole_0(k3_xboole_0(k3_xboole_0(A_84,B_85),C_86),k3_xboole_0(A_84,k4_xboole_0(B_85,C_86))) = k3_xboole_0(A_84,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_14])).

tff(c_401,plain,(
    ! [A_84,B_85,C_86] : k2_xboole_0(k3_xboole_0(A_84,k3_xboole_0(B_85,C_86)),k3_xboole_0(A_84,k4_xboole_0(B_85,C_86))) = k3_xboole_0(A_84,B_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_125])).

tff(c_213,plain,(
    ! [A_103,B_104,C_105] : r1_tarski(k2_xboole_0(k3_xboole_0(A_103,B_104),k3_xboole_0(A_103,C_105)),k2_xboole_0(B_104,C_105)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_225,plain,(
    ! [A_103,A_17,B_18] : r1_tarski(k2_xboole_0(k3_xboole_0(A_103,k3_xboole_0(A_17,B_18)),k3_xboole_0(A_103,k4_xboole_0(A_17,B_18))),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_213])).

tff(c_403,plain,(
    ! [A_103,A_17] : r1_tarski(k3_xboole_0(A_103,A_17),A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_225])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(A_50,k1_zfmisc_1(B_51))
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_86,plain,(
    ! [A_73,B_74] :
      ( v1_relat_1(A_73)
      | ~ v1_relat_1(B_74)
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_90,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k3_xboole_0(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,(
    ! [A_55,B_57] :
      ( r1_tarski(k2_relat_1(A_55),k2_relat_1(B_57))
      | ~ r1_tarski(A_55,B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_192,plain,(
    ! [A_96,B_97,C_98] :
      ( r1_tarski(A_96,k3_xboole_0(B_97,C_98))
      | ~ r1_tarski(A_96,C_98)
      | ~ r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_203,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_192,c_42])).

tff(c_289,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_292,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_289])).

tff(c_295,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6,c_292])).

tff(c_298,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_295])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_298])).

tff(c_303,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_307,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_303])).

tff(c_310,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_307])).

tff(c_325,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_328,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_325])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_328])).

tff(c_333,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.36  
% 2.46/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.36  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.46/1.36  
% 2.46/1.36  %Foreground sorts:
% 2.46/1.36  
% 2.46/1.36  
% 2.46/1.36  %Background operators:
% 2.46/1.36  
% 2.46/1.36  
% 2.46/1.36  %Foreground operators:
% 2.46/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.46/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.46/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.46/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.46/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.46/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.46/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.46/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.46/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.46/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.46/1.36  
% 2.71/1.37  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.71/1.37  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.71/1.37  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.71/1.37  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.71/1.37  tff(f_89, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 2.71/1.37  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.71/1.37  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.71/1.37  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.71/1.37  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.71/1.37  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.71/1.37  tff(c_4, plain, (![A_3, B_4, C_5]: (k3_xboole_0(k3_xboole_0(A_3, B_4), C_5)=k3_xboole_0(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.71/1.37  tff(c_119, plain, (![A_84, B_85, C_86]: (k4_xboole_0(k3_xboole_0(A_84, B_85), C_86)=k3_xboole_0(A_84, k4_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.37  tff(c_14, plain, (![A_17, B_18]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.37  tff(c_125, plain, (![A_84, B_85, C_86]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(A_84, B_85), C_86), k3_xboole_0(A_84, k4_xboole_0(B_85, C_86)))=k3_xboole_0(A_84, B_85))), inference(superposition, [status(thm), theory('equality')], [c_119, c_14])).
% 2.71/1.37  tff(c_401, plain, (![A_84, B_85, C_86]: (k2_xboole_0(k3_xboole_0(A_84, k3_xboole_0(B_85, C_86)), k3_xboole_0(A_84, k4_xboole_0(B_85, C_86)))=k3_xboole_0(A_84, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_125])).
% 2.71/1.37  tff(c_213, plain, (![A_103, B_104, C_105]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_103, B_104), k3_xboole_0(A_103, C_105)), k2_xboole_0(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.71/1.37  tff(c_225, plain, (![A_103, A_17, B_18]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_103, k3_xboole_0(A_17, B_18)), k3_xboole_0(A_103, k4_xboole_0(A_17, B_18))), A_17))), inference(superposition, [status(thm), theory('equality')], [c_14, c_213])).
% 2.71/1.37  tff(c_403, plain, (![A_103, A_17]: (r1_tarski(k3_xboole_0(A_103, A_17), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_225])).
% 2.71/1.37  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.71/1.37  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.37  tff(c_34, plain, (![A_50, B_51]: (m1_subset_1(A_50, k1_zfmisc_1(B_51)) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.71/1.37  tff(c_81, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.71/1.37  tff(c_86, plain, (![A_73, B_74]: (v1_relat_1(A_73) | ~v1_relat_1(B_74) | ~r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_34, c_81])).
% 2.71/1.37  tff(c_90, plain, (![A_6, B_7]: (v1_relat_1(k3_xboole_0(A_6, B_7)) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_6, c_86])).
% 2.71/1.37  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.71/1.37  tff(c_38, plain, (![A_55, B_57]: (r1_tarski(k2_relat_1(A_55), k2_relat_1(B_57)) | ~r1_tarski(A_55, B_57) | ~v1_relat_1(B_57) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.71/1.37  tff(c_192, plain, (![A_96, B_97, C_98]: (r1_tarski(A_96, k3_xboole_0(B_97, C_98)) | ~r1_tarski(A_96, C_98) | ~r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.71/1.37  tff(c_42, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.71/1.37  tff(c_203, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_192, c_42])).
% 2.71/1.37  tff(c_289, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_203])).
% 2.71/1.37  tff(c_292, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_289])).
% 2.71/1.37  tff(c_295, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6, c_292])).
% 2.71/1.37  tff(c_298, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_90, c_295])).
% 2.71/1.37  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_298])).
% 2.71/1.37  tff(c_303, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_203])).
% 2.71/1.37  tff(c_307, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_303])).
% 2.71/1.37  tff(c_310, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_307])).
% 2.71/1.37  tff(c_325, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_310])).
% 2.71/1.37  tff(c_328, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_90, c_325])).
% 2.71/1.37  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_328])).
% 2.71/1.37  tff(c_333, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_310])).
% 2.71/1.37  tff(c_444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_403, c_333])).
% 2.71/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.37  
% 2.71/1.37  Inference rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Ref     : 0
% 2.71/1.37  #Sup     : 85
% 2.71/1.37  #Fact    : 0
% 2.71/1.37  #Define  : 0
% 2.71/1.37  #Split   : 3
% 2.71/1.37  #Chain   : 0
% 2.71/1.37  #Close   : 0
% 2.71/1.37  
% 2.71/1.37  Ordering : KBO
% 2.71/1.37  
% 2.71/1.37  Simplification rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Subsume      : 2
% 2.71/1.37  #Demod        : 52
% 2.71/1.37  #Tautology    : 32
% 2.71/1.37  #SimpNegUnit  : 0
% 2.71/1.37  #BackRed      : 3
% 2.71/1.37  
% 2.71/1.37  #Partial instantiations: 0
% 2.71/1.37  #Strategies tried      : 1
% 2.71/1.37  
% 2.71/1.37  Timing (in seconds)
% 2.71/1.37  ----------------------
% 2.71/1.38  Preprocessing        : 0.32
% 2.71/1.38  Parsing              : 0.17
% 2.71/1.38  CNF conversion       : 0.02
% 2.71/1.38  Main loop            : 0.27
% 2.71/1.38  Inferencing          : 0.10
% 2.71/1.38  Reduction            : 0.09
% 2.71/1.38  Demodulation         : 0.07
% 2.71/1.38  BG Simplification    : 0.02
% 2.71/1.38  Subsumption          : 0.05
% 2.71/1.38  Abstraction          : 0.02
% 2.71/1.38  MUC search           : 0.00
% 2.71/1.38  Cooper               : 0.00
% 2.71/1.38  Total                : 0.61
% 2.71/1.38  Index Insertion      : 0.00
% 2.71/1.38  Index Deletion       : 0.00
% 2.71/1.38  Index Matching       : 0.00
% 2.71/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
