%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:31 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   55 (  77 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 135 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_64,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_61,plain,(
    ! [B_34,A_35] :
      ( r2_hidden(B_34,A_35)
      | ~ m1_subset_1(B_34,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_65,plain,(
    ! [B_34,A_9] :
      ( r1_tarski(B_34,A_9)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_61,c_8])).

tff(c_69,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(B_36,A_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_65])).

tff(c_82,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_81,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_69])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_206,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(k2_xboole_0(A_53,C_54),B_55)
      | ~ r1_tarski(C_54,B_55)
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_83,plain,(
    ! [B_38,A_39] :
      ( m1_subset_1(B_38,A_39)
      | ~ r2_hidden(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    ! [C_13,A_9] :
      ( m1_subset_1(C_13,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_10,c_83])).

tff(c_93,plain,(
    ! [C_13,A_9] :
      ( m1_subset_1(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_89])).

tff(c_104,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k3_subset_1(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_118,plain,(
    ! [A_9,C_13] :
      ( k4_xboole_0(A_9,C_13) = k3_subset_1(A_9,C_13)
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_93,c_104])).

tff(c_744,plain,(
    ! [B_111,A_112,C_113] :
      ( k4_xboole_0(B_111,k2_xboole_0(A_112,C_113)) = k3_subset_1(B_111,k2_xboole_0(A_112,C_113))
      | ~ r1_tarski(C_113,B_111)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(resolution,[status(thm)],[c_206,c_118])).

tff(c_121,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_104])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( r1_tarski(k4_xboole_0(C_3,B_2),k4_xboole_0(C_3,A_1))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_138,plain,(
    ! [B_2] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_2),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_2])).

tff(c_1399,plain,(
    ! [A_140,C_141] :
      ( r1_tarski(k3_subset_1('#skF_3',k2_xboole_0(A_140,C_141)),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',k2_xboole_0(A_140,C_141))
      | ~ r1_tarski(C_141,'#skF_3')
      | ~ r1_tarski(A_140,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_138])).

tff(c_302,plain,(
    ! [A_73,B_74,C_75] :
      ( k4_subset_1(A_73,B_74,C_75) = k2_xboole_0(B_74,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_316,plain,(
    ! [B_76] :
      ( k4_subset_1('#skF_3',B_76,'#skF_5') = k2_xboole_0(B_76,'#skF_5')
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_36,c_302])).

tff(c_334,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_316])).

tff(c_34,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3',k4_subset_1('#skF_3','#skF_4','#skF_5')),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_339,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_34])).

tff(c_1404,plain,
    ( ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1399,c_339])).

tff(c_1412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81,c_4,c_1404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:28:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.56  
% 3.53/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.56  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.53/1.56  
% 3.53/1.56  %Foreground sorts:
% 3.53/1.56  
% 3.53/1.56  
% 3.53/1.56  %Background operators:
% 3.53/1.56  
% 3.53/1.56  
% 3.53/1.56  %Foreground operators:
% 3.53/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.56  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.53/1.56  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.53/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.53/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.53/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.53/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.56  
% 3.53/1.57  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 3.53/1.57  tff(f_64, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.53/1.57  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.53/1.57  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.53/1.57  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.53/1.57  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.53/1.57  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.53/1.57  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 3.53/1.57  tff(f_70, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.53/1.57  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.53/1.57  tff(c_30, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.53/1.57  tff(c_61, plain, (![B_34, A_35]: (r2_hidden(B_34, A_35) | ~m1_subset_1(B_34, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.53/1.57  tff(c_8, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.53/1.57  tff(c_65, plain, (![B_34, A_9]: (r1_tarski(B_34, A_9) | ~m1_subset_1(B_34, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_61, c_8])).
% 3.53/1.57  tff(c_69, plain, (![B_36, A_37]: (r1_tarski(B_36, A_37) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)))), inference(negUnitSimplification, [status(thm)], [c_30, c_65])).
% 3.53/1.57  tff(c_82, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_69])).
% 3.53/1.57  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.53/1.57  tff(c_81, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_69])).
% 3.53/1.57  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.57  tff(c_206, plain, (![A_53, C_54, B_55]: (r1_tarski(k2_xboole_0(A_53, C_54), B_55) | ~r1_tarski(C_54, B_55) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.53/1.57  tff(c_10, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.53/1.57  tff(c_83, plain, (![B_38, A_39]: (m1_subset_1(B_38, A_39) | ~r2_hidden(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.53/1.57  tff(c_89, plain, (![C_13, A_9]: (m1_subset_1(C_13, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_10, c_83])).
% 3.53/1.57  tff(c_93, plain, (![C_13, A_9]: (m1_subset_1(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(negUnitSimplification, [status(thm)], [c_30, c_89])).
% 3.53/1.57  tff(c_104, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k3_subset_1(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.53/1.57  tff(c_118, plain, (![A_9, C_13]: (k4_xboole_0(A_9, C_13)=k3_subset_1(A_9, C_13) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_93, c_104])).
% 3.53/1.57  tff(c_744, plain, (![B_111, A_112, C_113]: (k4_xboole_0(B_111, k2_xboole_0(A_112, C_113))=k3_subset_1(B_111, k2_xboole_0(A_112, C_113)) | ~r1_tarski(C_113, B_111) | ~r1_tarski(A_112, B_111))), inference(resolution, [status(thm)], [c_206, c_118])).
% 3.53/1.57  tff(c_121, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_104])).
% 3.53/1.57  tff(c_2, plain, (![C_3, B_2, A_1]: (r1_tarski(k4_xboole_0(C_3, B_2), k4_xboole_0(C_3, A_1)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.53/1.57  tff(c_138, plain, (![B_2]: (r1_tarski(k4_xboole_0('#skF_3', B_2), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_2))), inference(superposition, [status(thm), theory('equality')], [c_121, c_2])).
% 3.53/1.57  tff(c_1399, plain, (![A_140, C_141]: (r1_tarski(k3_subset_1('#skF_3', k2_xboole_0(A_140, C_141)), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', k2_xboole_0(A_140, C_141)) | ~r1_tarski(C_141, '#skF_3') | ~r1_tarski(A_140, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_744, c_138])).
% 3.53/1.57  tff(c_302, plain, (![A_73, B_74, C_75]: (k4_subset_1(A_73, B_74, C_75)=k2_xboole_0(B_74, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.53/1.57  tff(c_316, plain, (![B_76]: (k4_subset_1('#skF_3', B_76, '#skF_5')=k2_xboole_0(B_76, '#skF_5') | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_36, c_302])).
% 3.53/1.57  tff(c_334, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_316])).
% 3.53/1.57  tff(c_34, plain, (~r1_tarski(k3_subset_1('#skF_3', k4_subset_1('#skF_3', '#skF_4', '#skF_5')), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.53/1.57  tff(c_339, plain, (~r1_tarski(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_34])).
% 3.53/1.57  tff(c_1404, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1399, c_339])).
% 3.53/1.57  tff(c_1412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_81, c_4, c_1404])).
% 3.53/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.57  
% 3.53/1.57  Inference rules
% 3.53/1.57  ----------------------
% 3.53/1.57  #Ref     : 0
% 3.53/1.57  #Sup     : 299
% 3.53/1.57  #Fact    : 0
% 3.53/1.57  #Define  : 0
% 3.53/1.57  #Split   : 4
% 3.53/1.57  #Chain   : 0
% 3.53/1.57  #Close   : 0
% 3.53/1.57  
% 3.53/1.57  Ordering : KBO
% 3.53/1.57  
% 3.53/1.57  Simplification rules
% 3.53/1.57  ----------------------
% 3.53/1.57  #Subsume      : 35
% 3.53/1.57  #Demod        : 28
% 3.53/1.57  #Tautology    : 74
% 3.53/1.57  #SimpNegUnit  : 36
% 3.53/1.57  #BackRed      : 1
% 3.53/1.57  
% 3.53/1.57  #Partial instantiations: 0
% 3.53/1.57  #Strategies tried      : 1
% 3.53/1.57  
% 3.53/1.57  Timing (in seconds)
% 3.53/1.57  ----------------------
% 3.53/1.57  Preprocessing        : 0.31
% 3.53/1.57  Parsing              : 0.16
% 3.53/1.57  CNF conversion       : 0.02
% 3.53/1.57  Main loop            : 0.52
% 3.53/1.57  Inferencing          : 0.20
% 3.53/1.57  Reduction            : 0.14
% 3.53/1.57  Demodulation         : 0.09
% 3.53/1.57  BG Simplification    : 0.03
% 3.53/1.57  Subsumption          : 0.10
% 3.53/1.58  Abstraction          : 0.04
% 3.53/1.58  MUC search           : 0.00
% 3.53/1.58  Cooper               : 0.00
% 3.53/1.58  Total                : 0.85
% 3.53/1.58  Index Insertion      : 0.00
% 3.53/1.58  Index Deletion       : 0.00
% 3.53/1.58  Index Matching       : 0.00
% 3.53/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
