%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:46 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 117 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 168 expanded)
%              Number of equality atoms :    8 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

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

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_131,plain,(
    ! [A_94,B_95,C_96] : k3_xboole_0(k3_xboole_0(A_94,B_95),C_96) = k3_xboole_0(A_94,k3_xboole_0(B_95,C_96)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_149,plain,(
    ! [A_94,B_95,C_96] : k2_xboole_0(k3_xboole_0(A_94,k3_xboole_0(B_95,C_96)),k4_xboole_0(k3_xboole_0(A_94,B_95),C_96)) = k3_xboole_0(A_94,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_14])).

tff(c_163,plain,(
    ! [A_94,B_95,C_96] : k2_xboole_0(k3_xboole_0(A_94,k3_xboole_0(B_95,C_96)),k3_xboole_0(A_94,k4_xboole_0(B_95,C_96))) = k3_xboole_0(A_94,B_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_149])).

tff(c_201,plain,(
    ! [A_107,B_108,C_109] : r1_tarski(k2_xboole_0(k3_xboole_0(A_107,B_108),k3_xboole_0(A_107,C_109)),k2_xboole_0(B_108,C_109)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_213,plain,(
    ! [A_107,A_17,B_18] : r1_tarski(k2_xboole_0(k3_xboole_0(A_107,k3_xboole_0(A_17,B_18)),k3_xboole_0(A_107,k4_xboole_0(A_17,B_18))),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_201])).

tff(c_484,plain,(
    ! [A_162,A_163] : r1_tarski(k3_xboole_0(A_162,A_163),A_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_213])).

tff(c_34,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(A_50,k1_zfmisc_1(B_51))
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_99,plain,(
    ! [B_82,A_83] :
      ( v1_relat_1(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83))
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_103,plain,(
    ! [A_50,B_51] :
      ( v1_relat_1(A_50)
      | ~ v1_relat_1(B_51)
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_34,c_99])).

tff(c_491,plain,(
    ! [A_162,A_163] :
      ( v1_relat_1(k3_xboole_0(A_162,A_163))
      | ~ v1_relat_1(A_163) ) ),
    inference(resolution,[status(thm)],[c_484,c_103])).

tff(c_434,plain,(
    ! [A_107,A_17] : r1_tarski(k3_xboole_0(A_107,A_17),A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_213])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_473,plain,(
    ! [C_159,A_160,B_161] :
      ( r1_tarski(k5_relat_1(C_159,A_160),k5_relat_1(C_159,B_161))
      | ~ r1_tarski(A_160,B_161)
      | ~ v1_relat_1(C_159)
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_379,plain,(
    ! [A_143,A_144] : r1_tarski(k3_xboole_0(A_143,A_144),A_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_213])).

tff(c_386,plain,(
    ! [A_143,A_144] :
      ( v1_relat_1(k3_xboole_0(A_143,A_144))
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_379,c_103])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_395,plain,(
    ! [C_147,A_148,B_149] :
      ( r1_tarski(k5_relat_1(C_147,A_148),k5_relat_1(C_147,B_149))
      | ~ r1_tarski(A_148,B_149)
      | ~ v1_relat_1(C_147)
      | ~ v1_relat_1(B_149)
      | ~ v1_relat_1(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_217,plain,(
    ! [A_110,B_111,C_112] :
      ( r1_tarski(A_110,k3_xboole_0(B_111,C_112))
      | ~ r1_tarski(A_110,C_112)
      | ~ r1_tarski(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_228,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_217,c_40])).

tff(c_306,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_398,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_395,c_306])).

tff(c_404,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_6,c_398])).

tff(c_408,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_386,c_404])).

tff(c_415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_408])).

tff(c_416,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_476,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_473,c_416])).

tff(c_482,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_476])).

tff(c_533,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_482])).

tff(c_536,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_491,c_533])).

tff(c_543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.43  
% 2.58/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.43  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.58/1.43  
% 2.58/1.43  %Foreground sorts:
% 2.58/1.43  
% 2.58/1.43  
% 2.58/1.43  %Background operators:
% 2.58/1.43  
% 2.58/1.43  
% 2.58/1.43  %Foreground operators:
% 2.58/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.58/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.58/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.58/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.58/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.58/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.58/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.58/1.43  
% 2.58/1.44  tff(f_93, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 2.58/1.44  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.58/1.44  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.58/1.44  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.58/1.44  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.58/1.44  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.58/1.44  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.58/1.44  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 2.58/1.44  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.58/1.44  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.58/1.44  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.58/1.44  tff(c_12, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.44  tff(c_131, plain, (![A_94, B_95, C_96]: (k3_xboole_0(k3_xboole_0(A_94, B_95), C_96)=k3_xboole_0(A_94, k3_xboole_0(B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.58/1.44  tff(c_14, plain, (![A_17, B_18]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.44  tff(c_149, plain, (![A_94, B_95, C_96]: (k2_xboole_0(k3_xboole_0(A_94, k3_xboole_0(B_95, C_96)), k4_xboole_0(k3_xboole_0(A_94, B_95), C_96))=k3_xboole_0(A_94, B_95))), inference(superposition, [status(thm), theory('equality')], [c_131, c_14])).
% 2.58/1.44  tff(c_163, plain, (![A_94, B_95, C_96]: (k2_xboole_0(k3_xboole_0(A_94, k3_xboole_0(B_95, C_96)), k3_xboole_0(A_94, k4_xboole_0(B_95, C_96)))=k3_xboole_0(A_94, B_95))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_149])).
% 2.58/1.44  tff(c_201, plain, (![A_107, B_108, C_109]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_107, B_108), k3_xboole_0(A_107, C_109)), k2_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.44  tff(c_213, plain, (![A_107, A_17, B_18]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_107, k3_xboole_0(A_17, B_18)), k3_xboole_0(A_107, k4_xboole_0(A_17, B_18))), A_17))), inference(superposition, [status(thm), theory('equality')], [c_14, c_201])).
% 2.58/1.44  tff(c_484, plain, (![A_162, A_163]: (r1_tarski(k3_xboole_0(A_162, A_163), A_163))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_213])).
% 2.58/1.44  tff(c_34, plain, (![A_50, B_51]: (m1_subset_1(A_50, k1_zfmisc_1(B_51)) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.58/1.44  tff(c_99, plain, (![B_82, A_83]: (v1_relat_1(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.58/1.44  tff(c_103, plain, (![A_50, B_51]: (v1_relat_1(A_50) | ~v1_relat_1(B_51) | ~r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_34, c_99])).
% 2.58/1.44  tff(c_491, plain, (![A_162, A_163]: (v1_relat_1(k3_xboole_0(A_162, A_163)) | ~v1_relat_1(A_163))), inference(resolution, [status(thm)], [c_484, c_103])).
% 2.58/1.44  tff(c_434, plain, (![A_107, A_17]: (r1_tarski(k3_xboole_0(A_107, A_17), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_213])).
% 2.58/1.44  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.58/1.44  tff(c_473, plain, (![C_159, A_160, B_161]: (r1_tarski(k5_relat_1(C_159, A_160), k5_relat_1(C_159, B_161)) | ~r1_tarski(A_160, B_161) | ~v1_relat_1(C_159) | ~v1_relat_1(B_161) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.58/1.44  tff(c_379, plain, (![A_143, A_144]: (r1_tarski(k3_xboole_0(A_143, A_144), A_144))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_213])).
% 2.58/1.44  tff(c_386, plain, (![A_143, A_144]: (v1_relat_1(k3_xboole_0(A_143, A_144)) | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_379, c_103])).
% 2.58/1.44  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.58/1.44  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.44  tff(c_395, plain, (![C_147, A_148, B_149]: (r1_tarski(k5_relat_1(C_147, A_148), k5_relat_1(C_147, B_149)) | ~r1_tarski(A_148, B_149) | ~v1_relat_1(C_147) | ~v1_relat_1(B_149) | ~v1_relat_1(A_148))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.58/1.44  tff(c_217, plain, (![A_110, B_111, C_112]: (r1_tarski(A_110, k3_xboole_0(B_111, C_112)) | ~r1_tarski(A_110, C_112) | ~r1_tarski(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.58/1.44  tff(c_40, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.58/1.44  tff(c_228, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_217, c_40])).
% 2.58/1.44  tff(c_306, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_228])).
% 2.58/1.44  tff(c_398, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_395, c_306])).
% 2.58/1.44  tff(c_404, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_6, c_398])).
% 2.58/1.44  tff(c_408, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_386, c_404])).
% 2.58/1.44  tff(c_415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_408])).
% 2.58/1.44  tff(c_416, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_228])).
% 2.58/1.44  tff(c_476, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_473, c_416])).
% 2.58/1.44  tff(c_482, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_476])).
% 2.58/1.44  tff(c_533, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_482])).
% 2.58/1.44  tff(c_536, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_491, c_533])).
% 2.58/1.44  tff(c_543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_536])).
% 2.58/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.44  
% 2.58/1.44  Inference rules
% 2.58/1.44  ----------------------
% 2.58/1.44  #Ref     : 0
% 2.58/1.44  #Sup     : 112
% 2.58/1.44  #Fact    : 0
% 2.58/1.44  #Define  : 0
% 2.58/1.44  #Split   : 2
% 2.58/1.44  #Chain   : 0
% 2.58/1.44  #Close   : 0
% 2.58/1.44  
% 2.58/1.44  Ordering : KBO
% 2.58/1.44  
% 2.58/1.44  Simplification rules
% 2.58/1.44  ----------------------
% 2.58/1.45  #Subsume      : 6
% 2.58/1.45  #Demod        : 63
% 2.58/1.45  #Tautology    : 42
% 2.58/1.45  #SimpNegUnit  : 0
% 2.58/1.45  #BackRed      : 2
% 2.58/1.45  
% 2.58/1.45  #Partial instantiations: 0
% 2.58/1.45  #Strategies tried      : 1
% 2.58/1.45  
% 2.58/1.45  Timing (in seconds)
% 2.58/1.45  ----------------------
% 2.58/1.45  Preprocessing        : 0.34
% 2.58/1.45  Parsing              : 0.18
% 2.58/1.45  CNF conversion       : 0.02
% 2.58/1.45  Main loop            : 0.31
% 2.58/1.45  Inferencing          : 0.12
% 2.58/1.45  Reduction            : 0.10
% 2.58/1.45  Demodulation         : 0.07
% 2.58/1.45  BG Simplification    : 0.02
% 2.58/1.45  Subsumption          : 0.05
% 2.58/1.45  Abstraction          : 0.02
% 2.58/1.45  MUC search           : 0.00
% 2.58/1.45  Cooper               : 0.00
% 2.58/1.45  Total                : 0.68
% 2.58/1.45  Index Insertion      : 0.00
% 2.58/1.45  Index Deletion       : 0.00
% 2.58/1.45  Index Matching       : 0.00
% 2.58/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
