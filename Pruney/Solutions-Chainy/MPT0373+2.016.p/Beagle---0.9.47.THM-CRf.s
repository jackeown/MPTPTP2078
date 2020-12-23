%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:58 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   60 (  75 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 124 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_83,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_78,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_80,plain,(
    ! [B_57,A_58] :
      ( v1_xboole_0(B_57)
      | ~ m1_subset_1(B_57,A_58)
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_92,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_80])).

tff(c_93,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_34,plain,(
    ! [B_42,A_41] :
      ( r2_hidden(B_42,A_41)
      | ~ m1_subset_1(B_42,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k1_tarski(A_37),B_38)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_45] : ~ v1_xboole_0(k1_zfmisc_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [A_43] : k2_subset_1(A_43) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    ! [A_44] : m1_subset_1(k2_subset_1(A_44),k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_51,plain,(
    ! [A_44] : m1_subset_1(A_44,k1_zfmisc_1(A_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_30,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_zfmisc_1(A_39),k1_zfmisc_1(B_40))
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_169,plain,(
    ! [C_81,B_82,A_83] :
      ( r2_hidden(C_81,B_82)
      | ~ r2_hidden(C_81,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_244,plain,(
    ! [B_101,B_102,A_103] :
      ( r2_hidden(B_101,B_102)
      | ~ r1_tarski(A_103,B_102)
      | ~ m1_subset_1(B_101,A_103)
      | v1_xboole_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_34,c_169])).

tff(c_246,plain,(
    ! [B_101,B_40,A_39] :
      ( r2_hidden(B_101,k1_zfmisc_1(B_40))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_39))
      | v1_xboole_0(k1_zfmisc_1(A_39))
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_30,c_244])).

tff(c_284,plain,(
    ! [B_112,B_113,A_114] :
      ( r2_hidden(B_112,k1_zfmisc_1(B_113))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_114))
      | ~ r1_tarski(A_114,B_113) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_246])).

tff(c_298,plain,(
    ! [A_115,B_116] :
      ( r2_hidden(A_115,k1_zfmisc_1(B_116))
      | ~ r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_51,c_284])).

tff(c_32,plain,(
    ! [B_42,A_41] :
      ( m1_subset_1(B_42,A_41)
      | ~ r2_hidden(B_42,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_303,plain,(
    ! [A_115,B_116] :
      ( m1_subset_1(A_115,k1_zfmisc_1(B_116))
      | v1_xboole_0(k1_zfmisc_1(B_116))
      | ~ r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_298,c_32])).

tff(c_326,plain,(
    ! [A_123,B_124] :
      ( m1_subset_1(A_123,k1_zfmisc_1(B_124))
      | ~ r1_tarski(A_123,B_124) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_303])).

tff(c_46,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_344,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_326,c_46])).

tff(c_352,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_344])).

tff(c_355,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_352])).

tff(c_358,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_355])).

tff(c_360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_358])).

tff(c_362,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_369,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_362,c_8])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.28  
% 2.16/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.16/1.29  
% 2.16/1.29  %Foreground sorts:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Background operators:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Foreground operators:
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.16/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.29  
% 2.16/1.30  tff(f_91, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.16/1.30  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.16/1.30  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 2.16/1.30  tff(f_83, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.16/1.30  tff(f_78, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.16/1.30  tff(f_80, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.16/1.30  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.16/1.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.16/1.30  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.16/1.30  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.16/1.30  tff(c_50, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.16/1.30  tff(c_80, plain, (![B_57, A_58]: (v1_xboole_0(B_57) | ~m1_subset_1(B_57, A_58) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.30  tff(c_92, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_80])).
% 2.16/1.30  tff(c_93, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_92])).
% 2.16/1.30  tff(c_34, plain, (![B_42, A_41]: (r2_hidden(B_42, A_41) | ~m1_subset_1(B_42, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.30  tff(c_28, plain, (![A_37, B_38]: (r1_tarski(k1_tarski(A_37), B_38) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.30  tff(c_44, plain, (![A_45]: (~v1_xboole_0(k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.16/1.30  tff(c_40, plain, (![A_43]: (k2_subset_1(A_43)=A_43)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.30  tff(c_42, plain, (![A_44]: (m1_subset_1(k2_subset_1(A_44), k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.16/1.30  tff(c_51, plain, (![A_44]: (m1_subset_1(A_44, k1_zfmisc_1(A_44)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 2.16/1.30  tff(c_30, plain, (![A_39, B_40]: (r1_tarski(k1_zfmisc_1(A_39), k1_zfmisc_1(B_40)) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.30  tff(c_169, plain, (![C_81, B_82, A_83]: (r2_hidden(C_81, B_82) | ~r2_hidden(C_81, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.30  tff(c_244, plain, (![B_101, B_102, A_103]: (r2_hidden(B_101, B_102) | ~r1_tarski(A_103, B_102) | ~m1_subset_1(B_101, A_103) | v1_xboole_0(A_103))), inference(resolution, [status(thm)], [c_34, c_169])).
% 2.16/1.30  tff(c_246, plain, (![B_101, B_40, A_39]: (r2_hidden(B_101, k1_zfmisc_1(B_40)) | ~m1_subset_1(B_101, k1_zfmisc_1(A_39)) | v1_xboole_0(k1_zfmisc_1(A_39)) | ~r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_30, c_244])).
% 2.16/1.30  tff(c_284, plain, (![B_112, B_113, A_114]: (r2_hidden(B_112, k1_zfmisc_1(B_113)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_114)) | ~r1_tarski(A_114, B_113))), inference(negUnitSimplification, [status(thm)], [c_44, c_246])).
% 2.16/1.30  tff(c_298, plain, (![A_115, B_116]: (r2_hidden(A_115, k1_zfmisc_1(B_116)) | ~r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_51, c_284])).
% 2.16/1.30  tff(c_32, plain, (![B_42, A_41]: (m1_subset_1(B_42, A_41) | ~r2_hidden(B_42, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.16/1.30  tff(c_303, plain, (![A_115, B_116]: (m1_subset_1(A_115, k1_zfmisc_1(B_116)) | v1_xboole_0(k1_zfmisc_1(B_116)) | ~r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_298, c_32])).
% 2.16/1.30  tff(c_326, plain, (![A_123, B_124]: (m1_subset_1(A_123, k1_zfmisc_1(B_124)) | ~r1_tarski(A_123, B_124))), inference(negUnitSimplification, [status(thm)], [c_44, c_303])).
% 2.16/1.30  tff(c_46, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.16/1.30  tff(c_344, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_326, c_46])).
% 2.16/1.30  tff(c_352, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_344])).
% 2.16/1.30  tff(c_355, plain, (~m1_subset_1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_352])).
% 2.16/1.30  tff(c_358, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_355])).
% 2.16/1.30  tff(c_360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_358])).
% 2.16/1.30  tff(c_362, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_92])).
% 2.16/1.30  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.16/1.30  tff(c_369, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_362, c_8])).
% 2.16/1.30  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_369])).
% 2.16/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  Inference rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Ref     : 0
% 2.16/1.30  #Sup     : 67
% 2.16/1.30  #Fact    : 0
% 2.16/1.30  #Define  : 0
% 2.16/1.30  #Split   : 1
% 2.16/1.30  #Chain   : 0
% 2.16/1.30  #Close   : 0
% 2.16/1.30  
% 2.16/1.30  Ordering : KBO
% 2.16/1.30  
% 2.16/1.30  Simplification rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Subsume      : 16
% 2.16/1.30  #Demod        : 3
% 2.16/1.30  #Tautology    : 23
% 2.16/1.30  #SimpNegUnit  : 9
% 2.16/1.30  #BackRed      : 0
% 2.16/1.30  
% 2.16/1.30  #Partial instantiations: 0
% 2.16/1.30  #Strategies tried      : 1
% 2.16/1.30  
% 2.16/1.30  Timing (in seconds)
% 2.16/1.30  ----------------------
% 2.16/1.30  Preprocessing        : 0.31
% 2.16/1.30  Parsing              : 0.17
% 2.16/1.30  CNF conversion       : 0.02
% 2.16/1.30  Main loop            : 0.22
% 2.16/1.30  Inferencing          : 0.09
% 2.16/1.30  Reduction            : 0.06
% 2.16/1.30  Demodulation         : 0.04
% 2.16/1.30  BG Simplification    : 0.02
% 2.16/1.30  Subsumption          : 0.04
% 2.16/1.30  Abstraction          : 0.01
% 2.16/1.30  MUC search           : 0.00
% 2.16/1.30  Cooper               : 0.00
% 2.16/1.30  Total                : 0.57
% 2.16/1.30  Index Insertion      : 0.00
% 2.16/1.30  Index Deletion       : 0.00
% 2.16/1.30  Index Matching       : 0.00
% 2.16/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
