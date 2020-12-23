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
% DateTime   : Thu Dec  3 09:56:34 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   55 (  67 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 101 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

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

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

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

tff(c_103,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(B_44,C_43)
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_110,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,'#skF_3')
      | ~ r1_tarski(A_42,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_82,c_103])).

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

tff(c_241,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_279,plain,(
    ! [A_77,C_78] :
      ( k4_xboole_0(A_77,C_78) = k3_subset_1(A_77,C_78)
      | ~ r1_tarski(C_78,A_77) ) ),
    inference(resolution,[status(thm)],[c_93,c_241])).

tff(c_330,plain,(
    ! [A_79] :
      ( k4_xboole_0('#skF_3',A_79) = k3_subset_1('#skF_3',A_79)
      | ~ r1_tarski(A_79,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_110,c_279])).

tff(c_582,plain,(
    ! [B_104] : k4_xboole_0('#skF_3',k3_xboole_0('#skF_4',B_104)) = k3_subset_1('#skF_3',k3_xboole_0('#skF_4',B_104)) ),
    inference(resolution,[status(thm)],[c_2,c_330])).

tff(c_258,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_241])).

tff(c_6,plain,(
    ! [C_8,B_7,A_6] :
      ( r1_tarski(k4_xboole_0(C_8,B_7),k4_xboole_0(C_8,A_6))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_272,plain,(
    ! [A_6] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),k4_xboole_0('#skF_3',A_6))
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_6])).

tff(c_591,plain,(
    ! [B_104] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4',B_104)))
      | ~ r1_tarski(k3_xboole_0('#skF_4',B_104),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_272])).

tff(c_609,plain,(
    ! [B_104] : r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4',B_104))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_591])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_346,plain,(
    ! [A_80,B_81,C_82] :
      ( k9_subset_1(A_80,B_81,C_82) = k3_xboole_0(B_81,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_358,plain,(
    ! [B_81] : k9_subset_1('#skF_3',B_81,'#skF_5') = k3_xboole_0(B_81,'#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_346])).

tff(c_34,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k9_subset_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_360,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_34])).

tff(c_613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:30:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.36  
% 2.45/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.36  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.45/1.36  
% 2.45/1.36  %Foreground sorts:
% 2.45/1.36  
% 2.45/1.36  
% 2.45/1.36  %Background operators:
% 2.45/1.36  
% 2.45/1.36  
% 2.45/1.36  %Foreground operators:
% 2.45/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.45/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.45/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.45/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.45/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.36  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.45/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.36  
% 2.69/1.37  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.69/1.37  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 2.69/1.37  tff(f_64, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.69/1.37  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.69/1.37  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.69/1.37  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.69/1.37  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.69/1.37  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 2.69/1.37  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.69/1.37  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.37  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.69/1.37  tff(c_30, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.69/1.37  tff(c_61, plain, (![B_34, A_35]: (r2_hidden(B_34, A_35) | ~m1_subset_1(B_34, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.37  tff(c_8, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.69/1.37  tff(c_65, plain, (![B_34, A_9]: (r1_tarski(B_34, A_9) | ~m1_subset_1(B_34, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_61, c_8])).
% 2.69/1.37  tff(c_69, plain, (![B_36, A_37]: (r1_tarski(B_36, A_37) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)))), inference(negUnitSimplification, [status(thm)], [c_30, c_65])).
% 2.69/1.37  tff(c_82, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_69])).
% 2.69/1.37  tff(c_103, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(B_44, C_43) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.37  tff(c_110, plain, (![A_42]: (r1_tarski(A_42, '#skF_3') | ~r1_tarski(A_42, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_103])).
% 2.69/1.37  tff(c_10, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.69/1.37  tff(c_83, plain, (![B_38, A_39]: (m1_subset_1(B_38, A_39) | ~r2_hidden(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.37  tff(c_89, plain, (![C_13, A_9]: (m1_subset_1(C_13, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_10, c_83])).
% 2.69/1.37  tff(c_93, plain, (![C_13, A_9]: (m1_subset_1(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(negUnitSimplification, [status(thm)], [c_30, c_89])).
% 2.69/1.37  tff(c_241, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.69/1.37  tff(c_279, plain, (![A_77, C_78]: (k4_xboole_0(A_77, C_78)=k3_subset_1(A_77, C_78) | ~r1_tarski(C_78, A_77))), inference(resolution, [status(thm)], [c_93, c_241])).
% 2.69/1.37  tff(c_330, plain, (![A_79]: (k4_xboole_0('#skF_3', A_79)=k3_subset_1('#skF_3', A_79) | ~r1_tarski(A_79, '#skF_4'))), inference(resolution, [status(thm)], [c_110, c_279])).
% 2.69/1.37  tff(c_582, plain, (![B_104]: (k4_xboole_0('#skF_3', k3_xboole_0('#skF_4', B_104))=k3_subset_1('#skF_3', k3_xboole_0('#skF_4', B_104)))), inference(resolution, [status(thm)], [c_2, c_330])).
% 2.69/1.37  tff(c_258, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_241])).
% 2.69/1.37  tff(c_6, plain, (![C_8, B_7, A_6]: (r1_tarski(k4_xboole_0(C_8, B_7), k4_xboole_0(C_8, A_6)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.37  tff(c_272, plain, (![A_6]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k4_xboole_0('#skF_3', A_6)) | ~r1_tarski(A_6, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_258, c_6])).
% 2.69/1.37  tff(c_591, plain, (![B_104]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', B_104))) | ~r1_tarski(k3_xboole_0('#skF_4', B_104), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_582, c_272])).
% 2.69/1.37  tff(c_609, plain, (![B_104]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', B_104))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_591])).
% 2.69/1.37  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.69/1.37  tff(c_346, plain, (![A_80, B_81, C_82]: (k9_subset_1(A_80, B_81, C_82)=k3_xboole_0(B_81, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.37  tff(c_358, plain, (![B_81]: (k9_subset_1('#skF_3', B_81, '#skF_5')=k3_xboole_0(B_81, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_346])).
% 2.69/1.37  tff(c_34, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k9_subset_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.69/1.37  tff(c_360, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_34])).
% 2.69/1.37  tff(c_613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_609, c_360])).
% 2.69/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.37  
% 2.69/1.37  Inference rules
% 2.69/1.37  ----------------------
% 2.69/1.37  #Ref     : 0
% 2.69/1.38  #Sup     : 142
% 2.69/1.38  #Fact    : 0
% 2.69/1.38  #Define  : 0
% 2.69/1.38  #Split   : 4
% 2.69/1.38  #Chain   : 0
% 2.69/1.38  #Close   : 0
% 2.69/1.38  
% 2.69/1.38  Ordering : KBO
% 2.69/1.38  
% 2.69/1.38  Simplification rules
% 2.69/1.38  ----------------------
% 2.69/1.38  #Subsume      : 13
% 2.69/1.38  #Demod        : 15
% 2.69/1.38  #Tautology    : 28
% 2.69/1.38  #SimpNegUnit  : 2
% 2.69/1.38  #BackRed      : 2
% 2.69/1.38  
% 2.69/1.38  #Partial instantiations: 0
% 2.69/1.38  #Strategies tried      : 1
% 2.69/1.38  
% 2.69/1.38  Timing (in seconds)
% 2.69/1.38  ----------------------
% 2.69/1.38  Preprocessing        : 0.30
% 2.69/1.38  Parsing              : 0.16
% 2.69/1.38  CNF conversion       : 0.02
% 2.69/1.38  Main loop            : 0.31
% 2.69/1.38  Inferencing          : 0.12
% 2.69/1.38  Reduction            : 0.09
% 2.69/1.38  Demodulation         : 0.06
% 2.69/1.38  BG Simplification    : 0.02
% 2.69/1.38  Subsumption          : 0.06
% 2.69/1.38  Abstraction          : 0.02
% 2.69/1.38  MUC search           : 0.00
% 2.69/1.38  Cooper               : 0.00
% 2.69/1.38  Total                : 0.64
% 2.69/1.38  Index Insertion      : 0.00
% 2.69/1.38  Index Deletion       : 0.00
% 2.69/1.38  Index Matching       : 0.00
% 2.69/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
