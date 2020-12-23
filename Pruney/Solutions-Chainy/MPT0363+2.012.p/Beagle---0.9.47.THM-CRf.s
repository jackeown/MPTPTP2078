%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:37 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   61 (  75 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 124 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_88,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_508,plain,(
    ! [B_99,A_100] :
      ( r2_hidden(B_99,A_100)
      | ~ m1_subset_1(B_99,A_100)
      | v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_512,plain,(
    ! [B_99,A_13] :
      ( r1_tarski(B_99,A_13)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_508,c_16])).

tff(c_516,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(B_101,A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_102)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_512])).

tff(c_528,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_516])).

tff(c_48,plain,
    ( ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_77,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_284,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_297,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_284])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_xboole_0(k4_xboole_0(A_8,B_9),B_9) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_57,plain,(
    ! [B_31,A_32] :
      ( r1_xboole_0(B_31,A_32)
      | ~ r1_xboole_0(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    ! [B_9,A_8] : r1_xboole_0(B_9,k4_xboole_0(A_8,B_9)) ),
    inference(resolution,[status(thm)],[c_12,c_57])).

tff(c_313,plain,(
    r1_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_60])).

tff(c_54,plain,
    ( r1_xboole_0('#skF_4','#skF_5')
    | r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_103,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_54])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_4])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_xboole_0(A_5,B_6)
      | ~ r1_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_462,plain,(
    ! [A_94] :
      ( r1_xboole_0(A_94,'#skF_4')
      | ~ r1_xboole_0(A_94,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_10])).

tff(c_478,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_313,c_462])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_484,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_478,c_2])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_484])).

tff(c_490,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_947,plain,(
    ! [A_179,B_180] :
      ( k4_xboole_0(A_179,B_180) = k3_subset_1(A_179,B_180)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(A_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_968,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_947])).

tff(c_1171,plain,(
    ! [A_207,B_208,C_209] :
      ( r1_tarski(A_207,k4_xboole_0(B_208,C_209))
      | ~ r1_xboole_0(A_207,C_209)
      | ~ r1_tarski(A_207,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1206,plain,(
    ! [A_219] :
      ( r1_tarski(A_219,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_xboole_0(A_219,'#skF_5')
      | ~ r1_tarski(A_219,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_1171])).

tff(c_489,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1212,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1206,c_489])).

tff(c_1220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_490,c_1212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:00:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.52  
% 3.33/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.33/1.52  
% 3.33/1.52  %Foreground sorts:
% 3.33/1.52  
% 3.33/1.52  
% 3.33/1.52  %Background operators:
% 3.33/1.52  
% 3.33/1.52  
% 3.33/1.52  %Foreground operators:
% 3.33/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.33/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.33/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.33/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.33/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.33/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.33/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.52  
% 3.51/1.53  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 3.51/1.53  tff(f_88, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.51/1.53  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.51/1.53  tff(f_64, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.51/1.53  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.51/1.53  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.51/1.53  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.51/1.53  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.51/1.53  tff(f_49, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.51/1.53  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.51/1.53  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.51/1.53  tff(c_40, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.51/1.53  tff(c_508, plain, (![B_99, A_100]: (r2_hidden(B_99, A_100) | ~m1_subset_1(B_99, A_100) | v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.51/1.53  tff(c_16, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.51/1.53  tff(c_512, plain, (![B_99, A_13]: (r1_tarski(B_99, A_13) | ~m1_subset_1(B_99, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_508, c_16])).
% 3.51/1.53  tff(c_516, plain, (![B_101, A_102]: (r1_tarski(B_101, A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_102)))), inference(negUnitSimplification, [status(thm)], [c_40, c_512])).
% 3.51/1.53  tff(c_528, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_516])).
% 3.51/1.53  tff(c_48, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | ~r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.51/1.53  tff(c_77, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 3.51/1.53  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.51/1.53  tff(c_284, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.51/1.53  tff(c_297, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_284])).
% 3.51/1.53  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(k4_xboole_0(A_8, B_9), B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.51/1.53  tff(c_57, plain, (![B_31, A_32]: (r1_xboole_0(B_31, A_32) | ~r1_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.51/1.53  tff(c_60, plain, (![B_9, A_8]: (r1_xboole_0(B_9, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_12, c_57])).
% 3.51/1.53  tff(c_313, plain, (r1_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_297, c_60])).
% 3.51/1.53  tff(c_54, plain, (r1_xboole_0('#skF_4', '#skF_5') | r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.51/1.53  tff(c_103, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_77, c_54])).
% 3.51/1.53  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.51/1.53  tff(c_107, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_103, c_4])).
% 3.51/1.53  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_xboole_0(A_5, B_6) | ~r1_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.51/1.53  tff(c_462, plain, (![A_94]: (r1_xboole_0(A_94, '#skF_4') | ~r1_xboole_0(A_94, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_107, c_10])).
% 3.51/1.53  tff(c_478, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_313, c_462])).
% 3.51/1.53  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.51/1.53  tff(c_484, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_478, c_2])).
% 3.51/1.53  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_484])).
% 3.51/1.53  tff(c_490, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 3.51/1.53  tff(c_947, plain, (![A_179, B_180]: (k4_xboole_0(A_179, B_180)=k3_subset_1(A_179, B_180) | ~m1_subset_1(B_180, k1_zfmisc_1(A_179)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.51/1.53  tff(c_968, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_947])).
% 3.51/1.53  tff(c_1171, plain, (![A_207, B_208, C_209]: (r1_tarski(A_207, k4_xboole_0(B_208, C_209)) | ~r1_xboole_0(A_207, C_209) | ~r1_tarski(A_207, B_208))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.51/1.53  tff(c_1206, plain, (![A_219]: (r1_tarski(A_219, k3_subset_1('#skF_3', '#skF_5')) | ~r1_xboole_0(A_219, '#skF_5') | ~r1_tarski(A_219, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_968, c_1171])).
% 3.51/1.53  tff(c_489, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_48])).
% 3.51/1.53  tff(c_1212, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1206, c_489])).
% 3.51/1.53  tff(c_1220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_528, c_490, c_1212])).
% 3.51/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.53  
% 3.51/1.53  Inference rules
% 3.51/1.53  ----------------------
% 3.51/1.53  #Ref     : 0
% 3.51/1.53  #Sup     : 286
% 3.51/1.53  #Fact    : 0
% 3.51/1.53  #Define  : 0
% 3.51/1.53  #Split   : 1
% 3.51/1.53  #Chain   : 0
% 3.51/1.53  #Close   : 0
% 3.51/1.53  
% 3.51/1.53  Ordering : KBO
% 3.51/1.53  
% 3.51/1.53  Simplification rules
% 3.51/1.53  ----------------------
% 3.51/1.53  #Subsume      : 13
% 3.51/1.53  #Demod        : 101
% 3.51/1.53  #Tautology    : 147
% 3.51/1.53  #SimpNegUnit  : 7
% 3.51/1.53  #BackRed      : 0
% 3.51/1.53  
% 3.51/1.53  #Partial instantiations: 0
% 3.51/1.53  #Strategies tried      : 1
% 3.51/1.53  
% 3.51/1.53  Timing (in seconds)
% 3.51/1.53  ----------------------
% 3.51/1.54  Preprocessing        : 0.31
% 3.51/1.54  Parsing              : 0.16
% 3.51/1.54  CNF conversion       : 0.02
% 3.51/1.54  Main loop            : 0.45
% 3.51/1.54  Inferencing          : 0.16
% 3.51/1.54  Reduction            : 0.15
% 3.51/1.54  Demodulation         : 0.11
% 3.51/1.54  BG Simplification    : 0.02
% 3.51/1.54  Subsumption          : 0.08
% 3.51/1.54  Abstraction          : 0.02
% 3.51/1.54  MUC search           : 0.00
% 3.51/1.54  Cooper               : 0.00
% 3.51/1.54  Total                : 0.79
% 3.51/1.54  Index Insertion      : 0.00
% 3.51/1.54  Index Deletion       : 0.00
% 3.51/1.54  Index Matching       : 0.00
% 3.51/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
