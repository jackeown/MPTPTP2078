%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:37 EST 2020

% Result     : Theorem 14.63s
% Output     : CNFRefutation 14.85s
% Verified   : 
% Statistics : Number of formulae       :   63 (  77 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 ( 134 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_6 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_99,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_60,plain,(
    ! [A_33] : ~ v1_xboole_0(k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_21147,plain,(
    ! [B_738,A_739] :
      ( r2_hidden(B_738,A_739)
      | ~ m1_subset_1(B_738,A_739)
      | v1_xboole_0(A_739) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    ! [C_28,A_24] :
      ( r1_tarski(C_28,A_24)
      | ~ r2_hidden(C_28,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_21162,plain,(
    ! [B_738,A_24] :
      ( r1_tarski(B_738,A_24)
      | ~ m1_subset_1(B_738,k1_zfmisc_1(A_24))
      | v1_xboole_0(k1_zfmisc_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_21147,c_38])).

tff(c_21189,plain,(
    ! [B_742,A_743] :
      ( r1_tarski(B_742,A_743)
      | ~ m1_subset_1(B_742,k1_zfmisc_1(A_743)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_21162])).

tff(c_21206,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_21189])).

tff(c_66,plain,
    ( ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_9'))
    | ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_96,plain,(
    ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,
    ( r1_xboole_0('#skF_8','#skF_9')
    | r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_163,plain,(
    r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_72])).

tff(c_62,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_254,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = k3_subset_1(A_77,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_270,plain,(
    k4_xboole_0('#skF_7','#skF_9') = k3_subset_1('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_254])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_4'(A_14,B_15),B_15)
      | r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_4'(A_14,B_15),A_14)
      | r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_238,plain,(
    ! [C_74,B_75,A_76] :
      ( r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_816,plain,(
    ! [A_125,B_126,B_127] :
      ( r2_hidden('#skF_4'(A_125,B_126),B_127)
      | ~ r1_tarski(A_125,B_127)
      | r1_xboole_0(A_125,B_126) ) ),
    inference(resolution,[status(thm)],[c_32,c_238])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_19720,plain,(
    ! [A_687,B_688,B_689,A_690] :
      ( ~ r2_hidden('#skF_4'(A_687,B_688),B_689)
      | ~ r1_tarski(A_687,k4_xboole_0(A_690,B_689))
      | r1_xboole_0(A_687,B_688) ) ),
    inference(resolution,[status(thm)],[c_816,c_10])).

tff(c_19815,plain,(
    ! [A_694,A_695,B_696] :
      ( ~ r1_tarski(A_694,k4_xboole_0(A_695,B_696))
      | r1_xboole_0(A_694,B_696) ) ),
    inference(resolution,[status(thm)],[c_30,c_19720])).

tff(c_20921,plain,(
    ! [A_726] :
      ( ~ r1_tarski(A_726,k3_subset_1('#skF_7','#skF_9'))
      | r1_xboole_0(A_726,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_19815])).

tff(c_21040,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_163,c_20921])).

tff(c_21082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_21040])).

tff(c_21084,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_21277,plain,(
    ! [A_756,B_757] :
      ( k4_xboole_0(A_756,B_757) = k3_subset_1(A_756,B_757)
      | ~ m1_subset_1(B_757,k1_zfmisc_1(A_756)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_21293,plain,(
    k4_xboole_0('#skF_7','#skF_9') = k3_subset_1('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_21277])).

tff(c_21395,plain,(
    ! [A_763,B_764,C_765] :
      ( r1_tarski(A_763,k4_xboole_0(B_764,C_765))
      | ~ r1_xboole_0(A_763,C_765)
      | ~ r1_tarski(A_763,B_764) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_21529,plain,(
    ! [A_779] :
      ( r1_tarski(A_779,k3_subset_1('#skF_7','#skF_9'))
      | ~ r1_xboole_0(A_779,'#skF_9')
      | ~ r1_tarski(A_779,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21293,c_21395])).

tff(c_21083,plain,(
    ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_21535,plain,
    ( ~ r1_xboole_0('#skF_8','#skF_9')
    | ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_21529,c_21083])).

tff(c_21540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21206,c_21084,c_21535])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.63/6.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.63/6.26  
% 14.63/6.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.63/6.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_6 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 14.63/6.26  
% 14.63/6.26  %Foreground sorts:
% 14.63/6.26  
% 14.63/6.26  
% 14.63/6.26  %Background operators:
% 14.63/6.26  
% 14.63/6.26  
% 14.63/6.26  %Foreground operators:
% 14.63/6.26  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 14.63/6.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.63/6.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.63/6.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.63/6.26  tff('#skF_7', type, '#skF_7': $i).
% 14.63/6.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.63/6.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.63/6.26  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.63/6.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.63/6.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.63/6.26  tff('#skF_9', type, '#skF_9': $i).
% 14.63/6.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.63/6.26  tff('#skF_8', type, '#skF_8': $i).
% 14.63/6.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.63/6.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.63/6.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.63/6.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.63/6.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.63/6.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.63/6.26  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 14.63/6.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 14.63/6.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.63/6.26  
% 14.85/6.27  tff(f_109, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 14.85/6.27  tff(f_99, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 14.85/6.27  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 14.85/6.27  tff(f_79, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 14.85/6.27  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 14.85/6.27  tff(f_64, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 14.85/6.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.85/6.27  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 14.85/6.27  tff(f_72, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 14.85/6.27  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.85/6.27  tff(c_60, plain, (![A_33]: (~v1_xboole_0(k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.85/6.27  tff(c_21147, plain, (![B_738, A_739]: (r2_hidden(B_738, A_739) | ~m1_subset_1(B_738, A_739) | v1_xboole_0(A_739))), inference(cnfTransformation, [status(thm)], [f_92])).
% 14.85/6.27  tff(c_38, plain, (![C_28, A_24]: (r1_tarski(C_28, A_24) | ~r2_hidden(C_28, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.85/6.27  tff(c_21162, plain, (![B_738, A_24]: (r1_tarski(B_738, A_24) | ~m1_subset_1(B_738, k1_zfmisc_1(A_24)) | v1_xboole_0(k1_zfmisc_1(A_24)))), inference(resolution, [status(thm)], [c_21147, c_38])).
% 14.85/6.27  tff(c_21189, plain, (![B_742, A_743]: (r1_tarski(B_742, A_743) | ~m1_subset_1(B_742, k1_zfmisc_1(A_743)))), inference(negUnitSimplification, [status(thm)], [c_60, c_21162])).
% 14.85/6.27  tff(c_21206, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_21189])).
% 14.85/6.27  tff(c_66, plain, (~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_9')) | ~r1_xboole_0('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.85/6.27  tff(c_96, plain, (~r1_xboole_0('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_66])).
% 14.85/6.27  tff(c_72, plain, (r1_xboole_0('#skF_8', '#skF_9') | r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.85/6.27  tff(c_163, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_96, c_72])).
% 14.85/6.27  tff(c_62, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.85/6.27  tff(c_254, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=k3_subset_1(A_77, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.85/6.27  tff(c_270, plain, (k4_xboole_0('#skF_7', '#skF_9')=k3_subset_1('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_62, c_254])).
% 14.85/6.27  tff(c_30, plain, (![A_14, B_15]: (r2_hidden('#skF_4'(A_14, B_15), B_15) | r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.85/6.27  tff(c_32, plain, (![A_14, B_15]: (r2_hidden('#skF_4'(A_14, B_15), A_14) | r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.85/6.27  tff(c_238, plain, (![C_74, B_75, A_76]: (r2_hidden(C_74, B_75) | ~r2_hidden(C_74, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.85/6.27  tff(c_816, plain, (![A_125, B_126, B_127]: (r2_hidden('#skF_4'(A_125, B_126), B_127) | ~r1_tarski(A_125, B_127) | r1_xboole_0(A_125, B_126))), inference(resolution, [status(thm)], [c_32, c_238])).
% 14.85/6.27  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.85/6.27  tff(c_19720, plain, (![A_687, B_688, B_689, A_690]: (~r2_hidden('#skF_4'(A_687, B_688), B_689) | ~r1_tarski(A_687, k4_xboole_0(A_690, B_689)) | r1_xboole_0(A_687, B_688))), inference(resolution, [status(thm)], [c_816, c_10])).
% 14.85/6.27  tff(c_19815, plain, (![A_694, A_695, B_696]: (~r1_tarski(A_694, k4_xboole_0(A_695, B_696)) | r1_xboole_0(A_694, B_696))), inference(resolution, [status(thm)], [c_30, c_19720])).
% 14.85/6.27  tff(c_20921, plain, (![A_726]: (~r1_tarski(A_726, k3_subset_1('#skF_7', '#skF_9')) | r1_xboole_0(A_726, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_19815])).
% 14.85/6.27  tff(c_21040, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_163, c_20921])).
% 14.85/6.27  tff(c_21082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_21040])).
% 14.85/6.27  tff(c_21084, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_66])).
% 14.85/6.27  tff(c_21277, plain, (![A_756, B_757]: (k4_xboole_0(A_756, B_757)=k3_subset_1(A_756, B_757) | ~m1_subset_1(B_757, k1_zfmisc_1(A_756)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.85/6.27  tff(c_21293, plain, (k4_xboole_0('#skF_7', '#skF_9')=k3_subset_1('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_62, c_21277])).
% 14.85/6.27  tff(c_21395, plain, (![A_763, B_764, C_765]: (r1_tarski(A_763, k4_xboole_0(B_764, C_765)) | ~r1_xboole_0(A_763, C_765) | ~r1_tarski(A_763, B_764))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.85/6.27  tff(c_21529, plain, (![A_779]: (r1_tarski(A_779, k3_subset_1('#skF_7', '#skF_9')) | ~r1_xboole_0(A_779, '#skF_9') | ~r1_tarski(A_779, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_21293, c_21395])).
% 14.85/6.27  tff(c_21083, plain, (~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_66])).
% 14.85/6.27  tff(c_21535, plain, (~r1_xboole_0('#skF_8', '#skF_9') | ~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_21529, c_21083])).
% 14.85/6.27  tff(c_21540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21206, c_21084, c_21535])).
% 14.85/6.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.85/6.27  
% 14.85/6.27  Inference rules
% 14.85/6.27  ----------------------
% 14.85/6.27  #Ref     : 0
% 14.85/6.27  #Sup     : 4946
% 14.85/6.27  #Fact    : 0
% 14.85/6.27  #Define  : 0
% 14.85/6.27  #Split   : 15
% 14.85/6.27  #Chain   : 0
% 14.85/6.27  #Close   : 0
% 14.85/6.27  
% 14.85/6.27  Ordering : KBO
% 14.85/6.27  
% 14.85/6.27  Simplification rules
% 14.85/6.27  ----------------------
% 14.85/6.27  #Subsume      : 378
% 14.85/6.27  #Demod        : 1727
% 14.85/6.27  #Tautology    : 568
% 14.85/6.27  #SimpNegUnit  : 50
% 14.85/6.27  #BackRed      : 0
% 14.85/6.27  
% 14.85/6.27  #Partial instantiations: 0
% 14.85/6.27  #Strategies tried      : 1
% 14.85/6.27  
% 14.85/6.27  Timing (in seconds)
% 14.85/6.27  ----------------------
% 14.85/6.28  Preprocessing        : 0.34
% 14.85/6.28  Parsing              : 0.17
% 14.85/6.28  CNF conversion       : 0.03
% 14.85/6.28  Main loop            : 5.17
% 14.85/6.28  Inferencing          : 1.03
% 14.85/6.28  Reduction            : 1.91
% 14.85/6.28  Demodulation         : 1.54
% 14.85/6.28  BG Simplification    : 0.13
% 14.85/6.28  Subsumption          : 1.70
% 14.85/6.28  Abstraction          : 0.16
% 14.85/6.28  MUC search           : 0.00
% 14.85/6.28  Cooper               : 0.00
% 14.85/6.28  Total                : 5.54
% 14.85/6.28  Index Insertion      : 0.00
% 14.85/6.28  Index Deletion       : 0.00
% 14.85/6.28  Index Matching       : 0.00
% 14.85/6.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
