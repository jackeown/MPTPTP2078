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
% DateTime   : Thu Dec  3 09:55:36 EST 2020

% Result     : Theorem 19.31s
% Output     : CNFRefutation 19.31s
% Verified   : 
% Statistics : Number of formulae       :   62 (  69 expanded)
%              Number of leaves         :   38 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 (  72 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_79,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_90,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_52,plain,(
    ! [A_52] : k2_subset_1(A_52) = A_52 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_62,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_65,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58,plain,(
    ! [A_57] : ~ v1_xboole_0(k1_zfmisc_1(A_57)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_241,plain,(
    ! [B_84,A_85] :
      ( r2_hidden(B_84,A_85)
      | ~ m1_subset_1(B_84,A_85)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [C_47,A_43] :
      ( r1_tarski(C_47,A_43)
      | ~ r2_hidden(C_47,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_248,plain,(
    ! [B_84,A_43] :
      ( r1_tarski(B_84,A_43)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_43))
      | v1_xboole_0(k1_zfmisc_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_241,c_30])).

tff(c_258,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(B_88,A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_89)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_248])).

tff(c_271,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_258])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_275,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_271,c_6])).

tff(c_781,plain,(
    ! [A_112,B_113] :
      ( k4_xboole_0(A_112,B_113) = k3_subset_1(A_112,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_798,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_781])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_802,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_798,c_8])).

tff(c_805,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_802])).

tff(c_56,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k3_subset_1(A_55,B_56),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2985,plain,(
    ! [A_166,B_167,C_168] :
      ( k4_subset_1(A_166,B_167,C_168) = k2_xboole_0(B_167,C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(A_166))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46272,plain,(
    ! [A_352,B_353,B_354] :
      ( k4_subset_1(A_352,B_353,k3_subset_1(A_352,B_354)) = k2_xboole_0(B_353,k3_subset_1(A_352,B_354))
      | ~ m1_subset_1(B_353,k1_zfmisc_1(A_352))
      | ~ m1_subset_1(B_354,k1_zfmisc_1(A_352)) ) ),
    inference(resolution,[status(thm)],[c_56,c_2985])).

tff(c_46295,plain,(
    ! [B_355] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_355)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_355))
      | ~ m1_subset_1(B_355,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_64,c_46272])).

tff(c_46314,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_46295])).

tff(c_46322,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_46314])).

tff(c_46324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_46322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:27:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.31/11.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.31/11.93  
% 19.31/11.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.31/11.93  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 19.31/11.93  
% 19.31/11.93  %Foreground sorts:
% 19.31/11.93  
% 19.31/11.93  
% 19.31/11.93  %Background operators:
% 19.31/11.93  
% 19.31/11.93  
% 19.31/11.93  %Foreground operators:
% 19.31/11.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.31/11.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.31/11.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 19.31/11.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.31/11.93  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 19.31/11.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 19.31/11.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.31/11.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.31/11.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.31/11.93  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 19.31/11.93  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 19.31/11.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.31/11.93  tff('#skF_3', type, '#skF_3': $i).
% 19.31/11.93  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 19.31/11.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.31/11.93  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 19.31/11.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.31/11.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 19.31/11.93  tff('#skF_4', type, '#skF_4': $i).
% 19.31/11.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.31/11.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 19.31/11.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.31/11.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.31/11.93  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 19.31/11.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.31/11.93  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 19.31/11.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.31/11.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.31/11.93  
% 19.31/11.94  tff(f_79, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 19.31/11.94  tff(f_101, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 19.31/11.94  tff(f_90, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 19.31/11.94  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 19.31/11.94  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 19.31/11.94  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 19.31/11.94  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 19.31/11.94  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 19.31/11.94  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 19.31/11.94  tff(f_96, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 19.31/11.94  tff(c_52, plain, (![A_52]: (k2_subset_1(A_52)=A_52)), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.31/11.94  tff(c_62, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 19.31/11.94  tff(c_65, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62])).
% 19.31/11.94  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 19.31/11.94  tff(c_58, plain, (![A_57]: (~v1_xboole_0(k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 19.31/11.94  tff(c_241, plain, (![B_84, A_85]: (r2_hidden(B_84, A_85) | ~m1_subset_1(B_84, A_85) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_77])).
% 19.31/11.94  tff(c_30, plain, (![C_47, A_43]: (r1_tarski(C_47, A_43) | ~r2_hidden(C_47, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 19.31/11.94  tff(c_248, plain, (![B_84, A_43]: (r1_tarski(B_84, A_43) | ~m1_subset_1(B_84, k1_zfmisc_1(A_43)) | v1_xboole_0(k1_zfmisc_1(A_43)))), inference(resolution, [status(thm)], [c_241, c_30])).
% 19.31/11.94  tff(c_258, plain, (![B_88, A_89]: (r1_tarski(B_88, A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(A_89)))), inference(negUnitSimplification, [status(thm)], [c_58, c_248])).
% 19.31/11.94  tff(c_271, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_258])).
% 19.31/11.94  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.31/11.94  tff(c_275, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_271, c_6])).
% 19.31/11.94  tff(c_781, plain, (![A_112, B_113]: (k4_xboole_0(A_112, B_113)=k3_subset_1(A_112, B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 19.31/11.94  tff(c_798, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_781])).
% 19.31/11.94  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.31/11.94  tff(c_802, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_798, c_8])).
% 19.31/11.94  tff(c_805, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_802])).
% 19.31/11.94  tff(c_56, plain, (![A_55, B_56]: (m1_subset_1(k3_subset_1(A_55, B_56), k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.31/11.94  tff(c_2985, plain, (![A_166, B_167, C_168]: (k4_subset_1(A_166, B_167, C_168)=k2_xboole_0(B_167, C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(A_166)) | ~m1_subset_1(B_167, k1_zfmisc_1(A_166)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.31/11.94  tff(c_46272, plain, (![A_352, B_353, B_354]: (k4_subset_1(A_352, B_353, k3_subset_1(A_352, B_354))=k2_xboole_0(B_353, k3_subset_1(A_352, B_354)) | ~m1_subset_1(B_353, k1_zfmisc_1(A_352)) | ~m1_subset_1(B_354, k1_zfmisc_1(A_352)))), inference(resolution, [status(thm)], [c_56, c_2985])).
% 19.31/11.94  tff(c_46295, plain, (![B_355]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_355))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_355)) | ~m1_subset_1(B_355, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_64, c_46272])).
% 19.31/11.94  tff(c_46314, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_46295])).
% 19.31/11.94  tff(c_46322, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_805, c_46314])).
% 19.31/11.94  tff(c_46324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_46322])).
% 19.31/11.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.31/11.94  
% 19.31/11.94  Inference rules
% 19.31/11.94  ----------------------
% 19.31/11.94  #Ref     : 0
% 19.31/11.94  #Sup     : 12571
% 19.31/11.94  #Fact    : 0
% 19.31/11.94  #Define  : 0
% 19.31/11.94  #Split   : 0
% 19.31/11.94  #Chain   : 0
% 19.31/11.94  #Close   : 0
% 19.31/11.94  
% 19.31/11.94  Ordering : KBO
% 19.31/11.94  
% 19.31/11.94  Simplification rules
% 19.31/11.94  ----------------------
% 19.31/11.94  #Subsume      : 558
% 19.31/11.94  #Demod        : 14334
% 19.31/11.94  #Tautology    : 3912
% 19.31/11.94  #SimpNegUnit  : 14
% 19.31/11.94  #BackRed      : 3
% 19.31/11.94  
% 19.31/11.94  #Partial instantiations: 0
% 19.31/11.94  #Strategies tried      : 1
% 19.31/11.94  
% 19.31/11.94  Timing (in seconds)
% 19.31/11.94  ----------------------
% 19.31/11.94  Preprocessing        : 0.37
% 19.31/11.94  Parsing              : 0.19
% 19.31/11.94  CNF conversion       : 0.02
% 19.31/11.94  Main loop            : 10.80
% 19.31/11.95  Inferencing          : 1.16
% 19.31/11.95  Reduction            : 7.76
% 19.31/11.95  Demodulation         : 7.34
% 19.31/11.95  BG Simplification    : 0.22
% 19.31/11.95  Subsumption          : 1.35
% 19.31/11.95  Abstraction          : 0.31
% 19.31/11.95  MUC search           : 0.00
% 19.31/11.95  Cooper               : 0.00
% 19.31/11.95  Total                : 11.19
% 19.31/11.95  Index Insertion      : 0.00
% 19.31/11.95  Index Deletion       : 0.00
% 19.31/11.95  Index Matching       : 0.00
% 19.31/11.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
