%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:52 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   68 (  99 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 177 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_44,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_82,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,(
    ! [A_25] : ~ v1_xboole_0(k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_97,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,A_51)
      | ~ m1_subset_1(B_50,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [C_18,A_14] :
      ( r1_tarski(C_18,A_14)
      | ~ r2_hidden(C_18,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_104,plain,(
    ! [B_50,A_14] :
      ( r1_tarski(B_50,A_14)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(resolution,[status(thm)],[c_97,c_14])).

tff(c_109,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_104])).

tff(c_126,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_109])).

tff(c_50,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_127,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_50])).

tff(c_137,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k3_subset_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_154,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_137])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_482,plain,(
    ! [A_104] :
      ( r1_xboole_0(A_104,'#skF_4')
      | ~ r1_tarski(A_104,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_4])).

tff(c_497,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_127,c_482])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_545,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_497,c_2])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_125,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_109])).

tff(c_153,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_137])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_272,plain,(
    ! [A_70,B_71,C_72] :
      ( r1_tarski(A_70,B_71)
      | ~ r1_xboole_0(A_70,C_72)
      | ~ r1_tarski(A_70,k2_xboole_0(B_71,C_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_714,plain,(
    ! [A_131,A_132,B_133] :
      ( r1_tarski(A_131,A_132)
      | ~ r1_xboole_0(A_131,k4_xboole_0(B_133,A_132))
      | ~ r1_tarski(A_131,B_133)
      | ~ r1_tarski(A_132,B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_272])).

tff(c_755,plain,(
    ! [A_131] :
      ( r1_tarski(A_131,'#skF_5')
      | ~ r1_xboole_0(A_131,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_131,'#skF_3')
      | ~ r1_tarski('#skF_5','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_714])).

tff(c_1996,plain,(
    ! [A_191] :
      ( r1_tarski(A_191,'#skF_5')
      | ~ r1_xboole_0(A_191,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_191,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_755])).

tff(c_2014,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_545,c_1996])).

tff(c_2034,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_2014])).

tff(c_2036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2034])).

tff(c_2037,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2038,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2094,plain,(
    ! [A_208,B_209] :
      ( k4_xboole_0(A_208,B_209) = k3_subset_1(A_208,B_209)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(A_208)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2110,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_2094])).

tff(c_2111,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_2094])).

tff(c_2151,plain,(
    ! [C_211,B_212,A_213] :
      ( r1_tarski(k4_xboole_0(C_211,B_212),k4_xboole_0(C_211,A_213))
      | ~ r1_tarski(A_213,B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2648,plain,(
    ! [B_268] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_268),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2111,c_2151])).

tff(c_2663,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_2648])).

tff(c_2669,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2038,c_2663])).

tff(c_2671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2037,c_2669])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.04/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.75  
% 4.04/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.75  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.04/1.75  
% 4.04/1.75  %Foreground sorts:
% 4.04/1.75  
% 4.04/1.75  
% 4.04/1.75  %Background operators:
% 4.04/1.75  
% 4.04/1.75  
% 4.04/1.75  %Foreground operators:
% 4.04/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.04/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.04/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.04/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.04/1.75  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.04/1.75  tff('#skF_5', type, '#skF_5': $i).
% 4.04/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.04/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.04/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.04/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.75  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.04/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.04/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.04/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.04/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.04/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.04/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.04/1.75  
% 4.04/1.76  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 4.04/1.76  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.04/1.76  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.04/1.76  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.04/1.76  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.04/1.76  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.04/1.76  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.04/1.76  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 4.04/1.76  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.04/1.76  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 4.04/1.76  tff(c_44, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.04/1.76  tff(c_82, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 4.04/1.76  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.04/1.76  tff(c_38, plain, (![A_25]: (~v1_xboole_0(k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.04/1.76  tff(c_97, plain, (![B_50, A_51]: (r2_hidden(B_50, A_51) | ~m1_subset_1(B_50, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.04/1.76  tff(c_14, plain, (![C_18, A_14]: (r1_tarski(C_18, A_14) | ~r2_hidden(C_18, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.04/1.76  tff(c_104, plain, (![B_50, A_14]: (r1_tarski(B_50, A_14) | ~m1_subset_1(B_50, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(resolution, [status(thm)], [c_97, c_14])).
% 4.04/1.76  tff(c_109, plain, (![B_52, A_53]: (r1_tarski(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)))), inference(negUnitSimplification, [status(thm)], [c_38, c_104])).
% 4.04/1.76  tff(c_126, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_109])).
% 4.04/1.76  tff(c_50, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.04/1.76  tff(c_127, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_82, c_50])).
% 4.04/1.76  tff(c_137, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k3_subset_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.04/1.76  tff(c_154, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_137])).
% 4.04/1.76  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.04/1.76  tff(c_482, plain, (![A_104]: (r1_xboole_0(A_104, '#skF_4') | ~r1_tarski(A_104, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_154, c_4])).
% 4.04/1.76  tff(c_497, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_127, c_482])).
% 4.04/1.76  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.04/1.76  tff(c_545, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_497, c_2])).
% 4.04/1.76  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.04/1.76  tff(c_125, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_109])).
% 4.04/1.76  tff(c_153, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_137])).
% 4.04/1.76  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.04/1.76  tff(c_272, plain, (![A_70, B_71, C_72]: (r1_tarski(A_70, B_71) | ~r1_xboole_0(A_70, C_72) | ~r1_tarski(A_70, k2_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.04/1.76  tff(c_714, plain, (![A_131, A_132, B_133]: (r1_tarski(A_131, A_132) | ~r1_xboole_0(A_131, k4_xboole_0(B_133, A_132)) | ~r1_tarski(A_131, B_133) | ~r1_tarski(A_132, B_133))), inference(superposition, [status(thm), theory('equality')], [c_10, c_272])).
% 4.04/1.76  tff(c_755, plain, (![A_131]: (r1_tarski(A_131, '#skF_5') | ~r1_xboole_0(A_131, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_131, '#skF_3') | ~r1_tarski('#skF_5', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_714])).
% 4.04/1.76  tff(c_1996, plain, (![A_191]: (r1_tarski(A_191, '#skF_5') | ~r1_xboole_0(A_191, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_191, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_755])).
% 4.04/1.76  tff(c_2014, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_545, c_1996])).
% 4.04/1.76  tff(c_2034, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_2014])).
% 4.04/1.76  tff(c_2036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_2034])).
% 4.04/1.76  tff(c_2037, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 4.04/1.76  tff(c_2038, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 4.04/1.76  tff(c_2094, plain, (![A_208, B_209]: (k4_xboole_0(A_208, B_209)=k3_subset_1(A_208, B_209) | ~m1_subset_1(B_209, k1_zfmisc_1(A_208)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.04/1.76  tff(c_2110, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_2094])).
% 4.04/1.76  tff(c_2111, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_2094])).
% 4.04/1.76  tff(c_2151, plain, (![C_211, B_212, A_213]: (r1_tarski(k4_xboole_0(C_211, B_212), k4_xboole_0(C_211, A_213)) | ~r1_tarski(A_213, B_212))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.04/1.76  tff(c_2648, plain, (![B_268]: (r1_tarski(k4_xboole_0('#skF_3', B_268), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_268))), inference(superposition, [status(thm), theory('equality')], [c_2111, c_2151])).
% 4.04/1.76  tff(c_2663, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2110, c_2648])).
% 4.04/1.76  tff(c_2669, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2038, c_2663])).
% 4.04/1.76  tff(c_2671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2037, c_2669])).
% 4.04/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.76  
% 4.04/1.76  Inference rules
% 4.04/1.76  ----------------------
% 4.04/1.76  #Ref     : 0
% 4.04/1.76  #Sup     : 605
% 4.04/1.76  #Fact    : 0
% 4.04/1.76  #Define  : 0
% 4.04/1.76  #Split   : 5
% 4.04/1.76  #Chain   : 0
% 4.04/1.76  #Close   : 0
% 4.04/1.76  
% 4.04/1.76  Ordering : KBO
% 4.04/1.76  
% 4.04/1.76  Simplification rules
% 4.04/1.76  ----------------------
% 4.04/1.76  #Subsume      : 31
% 4.04/1.76  #Demod        : 151
% 4.04/1.76  #Tautology    : 166
% 4.04/1.76  #SimpNegUnit  : 14
% 4.04/1.76  #BackRed      : 0
% 4.04/1.76  
% 4.04/1.76  #Partial instantiations: 0
% 4.04/1.76  #Strategies tried      : 1
% 4.04/1.76  
% 4.04/1.76  Timing (in seconds)
% 4.04/1.76  ----------------------
% 4.04/1.76  Preprocessing        : 0.31
% 4.04/1.76  Parsing              : 0.16
% 4.04/1.76  CNF conversion       : 0.02
% 4.04/1.77  Main loop            : 0.68
% 4.04/1.77  Inferencing          : 0.24
% 4.04/1.77  Reduction            : 0.23
% 4.04/1.77  Demodulation         : 0.15
% 4.04/1.77  BG Simplification    : 0.03
% 4.04/1.77  Subsumption          : 0.13
% 4.04/1.77  Abstraction          : 0.03
% 4.04/1.77  MUC search           : 0.00
% 4.04/1.77  Cooper               : 0.00
% 4.04/1.77  Total                : 1.02
% 4.04/1.77  Index Insertion      : 0.00
% 4.04/1.77  Index Deletion       : 0.00
% 4.04/1.77  Index Matching       : 0.00
% 4.04/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
