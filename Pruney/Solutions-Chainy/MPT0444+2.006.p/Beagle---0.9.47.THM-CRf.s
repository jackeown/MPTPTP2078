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
% DateTime   : Thu Dec  3 09:58:21 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   52 (  90 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 133 expanded)
%              Number of equality atoms :    4 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    ! [A_38,B_39] : r1_tarski(k3_xboole_0(A_38,B_39),A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_6])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_129,plain,(
    ! [A_46,B_47] :
      ( v1_relat_1(A_46)
      | ~ v1_relat_1(B_47)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_18,c_124])).

tff(c_151,plain,(
    ! [A_51,B_52] :
      ( v1_relat_1(k3_xboole_0(A_51,B_52))
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_98,c_129])).

tff(c_154,plain,(
    ! [B_2,A_1] :
      ( v1_relat_1(k3_xboole_0(B_2,A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_151])).

tff(c_107,plain,(
    ! [A_40,B_41] : r1_tarski(k3_xboole_0(A_40,B_41),A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_6])).

tff(c_110,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_22,plain,(
    ! [A_22,B_24] :
      ( r1_tarski(k2_relat_1(A_22),k2_relat_1(B_24))
      | ~ r1_tarski(A_22,B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_169,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(A_57,k3_xboole_0(B_58,C_59))
      | ~ r1_tarski(A_57,C_59)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_183,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_169,c_26])).

tff(c_301,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_304,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_301])).

tff(c_307,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_98,c_304])).

tff(c_310,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_154,c_307])).

tff(c_317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_310])).

tff(c_318,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_322,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_318])).

tff(c_325,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_110,c_322])).

tff(c_328,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_154,c_325])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:44:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.33  
% 2.16/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.33  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.16/1.33  
% 2.16/1.33  %Foreground sorts:
% 2.16/1.33  
% 2.16/1.33  
% 2.16/1.33  %Background operators:
% 2.16/1.33  
% 2.16/1.33  
% 2.16/1.33  %Foreground operators:
% 2.16/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.16/1.33  
% 2.16/1.34  tff(f_73, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 2.16/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.16/1.34  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.16/1.34  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.16/1.34  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.16/1.34  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.16/1.34  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.16/1.35  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.16/1.35  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.16/1.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.35  tff(c_89, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.35  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.35  tff(c_98, plain, (![A_38, B_39]: (r1_tarski(k3_xboole_0(A_38, B_39), A_38))), inference(superposition, [status(thm), theory('equality')], [c_89, c_6])).
% 2.16/1.35  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.35  tff(c_124, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.16/1.35  tff(c_129, plain, (![A_46, B_47]: (v1_relat_1(A_46) | ~v1_relat_1(B_47) | ~r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_18, c_124])).
% 2.16/1.35  tff(c_151, plain, (![A_51, B_52]: (v1_relat_1(k3_xboole_0(A_51, B_52)) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_98, c_129])).
% 2.16/1.35  tff(c_154, plain, (![B_2, A_1]: (v1_relat_1(k3_xboole_0(B_2, A_1)) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_151])).
% 2.16/1.35  tff(c_107, plain, (![A_40, B_41]: (r1_tarski(k3_xboole_0(A_40, B_41), A_40))), inference(superposition, [status(thm), theory('equality')], [c_89, c_6])).
% 2.16/1.35  tff(c_110, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 2.16/1.35  tff(c_22, plain, (![A_22, B_24]: (r1_tarski(k2_relat_1(A_22), k2_relat_1(B_24)) | ~r1_tarski(A_22, B_24) | ~v1_relat_1(B_24) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.16/1.35  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.16/1.35  tff(c_169, plain, (![A_57, B_58, C_59]: (r1_tarski(A_57, k3_xboole_0(B_58, C_59)) | ~r1_tarski(A_57, C_59) | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.35  tff(c_26, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.16/1.35  tff(c_183, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_169, c_26])).
% 2.16/1.35  tff(c_301, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_183])).
% 2.16/1.35  tff(c_304, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_301])).
% 2.16/1.35  tff(c_307, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_98, c_304])).
% 2.16/1.35  tff(c_310, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_154, c_307])).
% 2.16/1.35  tff(c_317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_310])).
% 2.16/1.35  tff(c_318, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_183])).
% 2.16/1.35  tff(c_322, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_318])).
% 2.16/1.35  tff(c_325, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_110, c_322])).
% 2.16/1.35  tff(c_328, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_154, c_325])).
% 2.16/1.35  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_328])).
% 2.16/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.35  
% 2.16/1.35  Inference rules
% 2.16/1.35  ----------------------
% 2.16/1.35  #Ref     : 0
% 2.16/1.35  #Sup     : 73
% 2.16/1.35  #Fact    : 0
% 2.16/1.35  #Define  : 0
% 2.16/1.35  #Split   : 1
% 2.16/1.35  #Chain   : 0
% 2.16/1.35  #Close   : 0
% 2.16/1.35  
% 2.16/1.35  Ordering : KBO
% 2.16/1.35  
% 2.16/1.35  Simplification rules
% 2.16/1.35  ----------------------
% 2.16/1.35  #Subsume      : 10
% 2.16/1.35  #Demod        : 18
% 2.16/1.35  #Tautology    : 37
% 2.16/1.35  #SimpNegUnit  : 0
% 2.16/1.35  #BackRed      : 0
% 2.16/1.35  
% 2.16/1.35  #Partial instantiations: 0
% 2.16/1.35  #Strategies tried      : 1
% 2.16/1.35  
% 2.16/1.35  Timing (in seconds)
% 2.16/1.35  ----------------------
% 2.16/1.35  Preprocessing        : 0.29
% 2.16/1.35  Parsing              : 0.15
% 2.16/1.35  CNF conversion       : 0.02
% 2.16/1.35  Main loop            : 0.22
% 2.16/1.35  Inferencing          : 0.08
% 2.16/1.35  Reduction            : 0.08
% 2.16/1.35  Demodulation         : 0.06
% 2.16/1.35  BG Simplification    : 0.01
% 2.16/1.35  Subsumption          : 0.04
% 2.16/1.35  Abstraction          : 0.01
% 2.16/1.35  MUC search           : 0.00
% 2.16/1.35  Cooper               : 0.00
% 2.16/1.35  Total                : 0.54
% 2.16/1.35  Index Insertion      : 0.00
% 2.16/1.35  Index Deletion       : 0.00
% 2.16/1.35  Index Matching       : 0.00
% 2.16/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
