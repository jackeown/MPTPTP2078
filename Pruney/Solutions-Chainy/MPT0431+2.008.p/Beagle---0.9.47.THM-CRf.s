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
% DateTime   : Thu Dec  3 09:58:13 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 119 expanded)
%              Number of leaves         :   26 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 264 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v3_setfam_1(B,A)
              & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) )
           => ! [C] :
                ( ( v3_setfam_1(C,A)
                  & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A))) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A),B,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(c_38,plain,(
    v3_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_103,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(A_46,B_47)
      | ~ v3_setfam_1(B_47,A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_106,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | ~ v3_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_103])).

tff(c_112,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_106])).

tff(c_34,plain,(
    v3_setfam_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_109,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | ~ v3_setfam_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_103])).

tff(c_115,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_109])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(k1_tarski(A_9),B_10)
      | r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_188,plain,(
    ! [A_66,B_67,C_68] :
      ( k4_subset_1(A_66,B_67,C_68) = k2_xboole_0(B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_306,plain,(
    ! [B_71] :
      ( k4_subset_1(k1_zfmisc_1('#skF_1'),B_71,'#skF_3') = k2_xboole_0(B_71,'#skF_3')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_188])).

tff(c_326,plain,(
    k4_subset_1(k1_zfmisc_1('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_306])).

tff(c_30,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_328,plain,(
    ~ v3_setfam_1(k2_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_30])).

tff(c_22,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_subset_1(k4_subset_1(A_16,B_17,C_18),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_332,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_22])).

tff(c_336,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_332])).

tff(c_26,plain,(
    ! [B_23,A_22] :
      ( v3_setfam_1(B_23,A_22)
      | r2_hidden(A_22,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_348,plain,
    ( v3_setfam_1(k2_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | r2_hidden('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_336,c_26])).

tff(c_357,plain,(
    r2_hidden('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_348])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k1_tarski(A_7),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_116,plain,(
    ! [A_48,B_49,C_50] :
      ( r1_tarski(A_48,B_49)
      | ~ r1_xboole_0(A_48,C_50)
      | ~ r1_tarski(A_48,k2_xboole_0(B_49,C_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_7,B_49,C_50] :
      ( r1_tarski(k1_tarski(A_7),B_49)
      | ~ r1_xboole_0(k1_tarski(A_7),C_50)
      | ~ r2_hidden(A_7,k2_xboole_0(B_49,C_50)) ) ),
    inference(resolution,[status(thm)],[c_10,c_116])).

tff(c_366,plain,
    ( r1_tarski(k1_tarski('#skF_1'),'#skF_2')
    | ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_357,c_124])).

tff(c_404,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_407,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_404])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_407])).

tff(c_412,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | ~ r1_tarski(k1_tarski(A_7),B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_416,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_412,c_8])).

tff(c_420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.31  %$ v3_setfam_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.19/1.31  
% 2.19/1.31  %Foreground sorts:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Background operators:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Foreground operators:
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.19/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.31  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 2.19/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.31  
% 2.53/1.32  tff(f_87, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((v3_setfam_1(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A)))) => (![C]: ((v3_setfam_1(C, A) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A)))) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A), B, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_setfam_1)).
% 2.53/1.32  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 2.53/1.32  tff(f_44, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.53/1.32  tff(f_64, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.53/1.32  tff(f_58, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.53/1.32  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.53/1.32  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 2.53/1.32  tff(c_38, plain, (v3_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.32  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.32  tff(c_103, plain, (![A_46, B_47]: (~r2_hidden(A_46, B_47) | ~v3_setfam_1(B_47, A_46) | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.53/1.32  tff(c_106, plain, (~r2_hidden('#skF_1', '#skF_2') | ~v3_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_103])).
% 2.53/1.32  tff(c_112, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_106])).
% 2.53/1.32  tff(c_34, plain, (v3_setfam_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.32  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.32  tff(c_109, plain, (~r2_hidden('#skF_1', '#skF_3') | ~v3_setfam_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_103])).
% 2.53/1.32  tff(c_115, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_109])).
% 2.53/1.32  tff(c_12, plain, (![A_9, B_10]: (r1_xboole_0(k1_tarski(A_9), B_10) | r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.53/1.32  tff(c_188, plain, (![A_66, B_67, C_68]: (k4_subset_1(A_66, B_67, C_68)=k2_xboole_0(B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_66)) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.53/1.32  tff(c_306, plain, (![B_71]: (k4_subset_1(k1_zfmisc_1('#skF_1'), B_71, '#skF_3')=k2_xboole_0(B_71, '#skF_3') | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(resolution, [status(thm)], [c_32, c_188])).
% 2.53/1.32  tff(c_326, plain, (k4_subset_1(k1_zfmisc_1('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_306])).
% 2.53/1.32  tff(c_30, plain, (~v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.32  tff(c_328, plain, (~v3_setfam_1(k2_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_30])).
% 2.53/1.32  tff(c_22, plain, (![A_16, B_17, C_18]: (m1_subset_1(k4_subset_1(A_16, B_17, C_18), k1_zfmisc_1(A_16)) | ~m1_subset_1(C_18, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.53/1.32  tff(c_332, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_326, c_22])).
% 2.53/1.32  tff(c_336, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_332])).
% 2.53/1.32  tff(c_26, plain, (![B_23, A_22]: (v3_setfam_1(B_23, A_22) | r2_hidden(A_22, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.53/1.32  tff(c_348, plain, (v3_setfam_1(k2_xboole_0('#skF_2', '#skF_3'), '#skF_1') | r2_hidden('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_336, c_26])).
% 2.53/1.32  tff(c_357, plain, (r2_hidden('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_328, c_348])).
% 2.53/1.32  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.53/1.32  tff(c_116, plain, (![A_48, B_49, C_50]: (r1_tarski(A_48, B_49) | ~r1_xboole_0(A_48, C_50) | ~r1_tarski(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.32  tff(c_124, plain, (![A_7, B_49, C_50]: (r1_tarski(k1_tarski(A_7), B_49) | ~r1_xboole_0(k1_tarski(A_7), C_50) | ~r2_hidden(A_7, k2_xboole_0(B_49, C_50)))), inference(resolution, [status(thm)], [c_10, c_116])).
% 2.53/1.32  tff(c_366, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2') | ~r1_xboole_0(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_357, c_124])).
% 2.53/1.32  tff(c_404, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_366])).
% 2.53/1.32  tff(c_407, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_404])).
% 2.53/1.32  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_407])).
% 2.53/1.32  tff(c_412, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_366])).
% 2.53/1.32  tff(c_8, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | ~r1_tarski(k1_tarski(A_7), B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.53/1.32  tff(c_416, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_412, c_8])).
% 2.53/1.32  tff(c_420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_416])).
% 2.53/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.32  
% 2.53/1.32  Inference rules
% 2.53/1.32  ----------------------
% 2.53/1.32  #Ref     : 0
% 2.53/1.32  #Sup     : 87
% 2.53/1.32  #Fact    : 0
% 2.53/1.32  #Define  : 0
% 2.53/1.32  #Split   : 3
% 2.53/1.32  #Chain   : 0
% 2.53/1.32  #Close   : 0
% 2.53/1.32  
% 2.53/1.32  Ordering : KBO
% 2.53/1.32  
% 2.53/1.32  Simplification rules
% 2.53/1.32  ----------------------
% 2.53/1.32  #Subsume      : 8
% 2.53/1.32  #Demod        : 16
% 2.53/1.32  #Tautology    : 25
% 2.53/1.32  #SimpNegUnit  : 7
% 2.53/1.32  #BackRed      : 1
% 2.53/1.32  
% 2.53/1.32  #Partial instantiations: 0
% 2.53/1.32  #Strategies tried      : 1
% 2.53/1.32  
% 2.53/1.32  Timing (in seconds)
% 2.53/1.32  ----------------------
% 2.53/1.32  Preprocessing        : 0.30
% 2.53/1.32  Parsing              : 0.17
% 2.53/1.32  CNF conversion       : 0.02
% 2.53/1.32  Main loop            : 0.25
% 2.53/1.32  Inferencing          : 0.09
% 2.53/1.32  Reduction            : 0.08
% 2.53/1.32  Demodulation         : 0.05
% 2.53/1.32  BG Simplification    : 0.01
% 2.53/1.32  Subsumption          : 0.05
% 2.53/1.32  Abstraction          : 0.01
% 2.53/1.32  MUC search           : 0.00
% 2.53/1.32  Cooper               : 0.00
% 2.53/1.32  Total                : 0.58
% 2.53/1.32  Index Insertion      : 0.00
% 2.53/1.32  Index Deletion       : 0.00
% 2.53/1.32  Index Matching       : 0.00
% 2.53/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
