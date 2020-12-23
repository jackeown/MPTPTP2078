%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:37 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   51 (  89 expanded)
%              Number of leaves         :   24 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 131 expanded)
%              Number of equality atoms :    4 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

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

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [A_38,B_39] : r1_tarski(k3_xboole_0(A_38,B_39),A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_6])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_122,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_127,plain,(
    ! [A_46,B_47] :
      ( v1_relat_1(A_46)
      | ~ v1_relat_1(B_47)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_18,c_122])).

tff(c_149,plain,(
    ! [A_51,B_52] :
      ( v1_relat_1(k3_xboole_0(A_51,B_52))
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_96,c_127])).

tff(c_155,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k3_xboole_0(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_149])).

tff(c_105,plain,(
    ! [A_40,B_41] : r1_tarski(k3_xboole_0(A_40,B_41),A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_6])).

tff(c_108,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_105])).

tff(c_22,plain,(
    ! [A_22,B_24] :
      ( r1_tarski(k3_relat_1(A_22),k3_relat_1(B_24))
      | ~ r1_tarski(A_22,B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_167,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(A_57,k3_xboole_0(B_58,C_59))
      | ~ r1_tarski(A_57,C_59)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_181,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_167,c_24])).

tff(c_305,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_308,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_305])).

tff(c_311,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_96,c_308])).

tff(c_314,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_155,c_311])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_314])).

tff(c_322,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_326,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_322])).

tff(c_329,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_108,c_326])).

tff(c_332,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_155,c_329])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.24  
% 2.16/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.24  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 2.16/1.24  
% 2.16/1.24  %Foreground sorts:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Background operators:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Foreground operators:
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.16/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.16/1.24  
% 2.16/1.25  tff(f_71, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 2.16/1.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.16/1.25  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.16/1.25  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.16/1.25  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.16/1.25  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.16/1.25  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.16/1.25  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.16/1.25  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.16/1.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.25  tff(c_87, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.25  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.25  tff(c_96, plain, (![A_38, B_39]: (r1_tarski(k3_xboole_0(A_38, B_39), A_38))), inference(superposition, [status(thm), theory('equality')], [c_87, c_6])).
% 2.16/1.25  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.25  tff(c_122, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.16/1.25  tff(c_127, plain, (![A_46, B_47]: (v1_relat_1(A_46) | ~v1_relat_1(B_47) | ~r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_18, c_122])).
% 2.16/1.25  tff(c_149, plain, (![A_51, B_52]: (v1_relat_1(k3_xboole_0(A_51, B_52)) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_96, c_127])).
% 2.16/1.25  tff(c_155, plain, (![A_1, B_2]: (v1_relat_1(k3_xboole_0(A_1, B_2)) | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_149])).
% 2.16/1.25  tff(c_105, plain, (![A_40, B_41]: (r1_tarski(k3_xboole_0(A_40, B_41), A_40))), inference(superposition, [status(thm), theory('equality')], [c_87, c_6])).
% 2.16/1.25  tff(c_108, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_105])).
% 2.16/1.25  tff(c_22, plain, (![A_22, B_24]: (r1_tarski(k3_relat_1(A_22), k3_relat_1(B_24)) | ~r1_tarski(A_22, B_24) | ~v1_relat_1(B_24) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.25  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.16/1.25  tff(c_167, plain, (![A_57, B_58, C_59]: (r1_tarski(A_57, k3_xboole_0(B_58, C_59)) | ~r1_tarski(A_57, C_59) | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.25  tff(c_24, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.16/1.25  tff(c_181, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_167, c_24])).
% 2.16/1.25  tff(c_305, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_181])).
% 2.16/1.25  tff(c_308, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_305])).
% 2.16/1.25  tff(c_311, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_96, c_308])).
% 2.16/1.25  tff(c_314, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_155, c_311])).
% 2.16/1.25  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_314])).
% 2.16/1.25  tff(c_322, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_181])).
% 2.16/1.25  tff(c_326, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_322])).
% 2.16/1.25  tff(c_329, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_108, c_326])).
% 2.16/1.25  tff(c_332, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_155, c_329])).
% 2.16/1.25  tff(c_339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_332])).
% 2.16/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.25  
% 2.16/1.25  Inference rules
% 2.16/1.25  ----------------------
% 2.16/1.25  #Ref     : 0
% 2.16/1.25  #Sup     : 76
% 2.16/1.25  #Fact    : 0
% 2.16/1.25  #Define  : 0
% 2.16/1.25  #Split   : 1
% 2.16/1.25  #Chain   : 0
% 2.16/1.25  #Close   : 0
% 2.16/1.25  
% 2.16/1.25  Ordering : KBO
% 2.16/1.25  
% 2.16/1.25  Simplification rules
% 2.16/1.25  ----------------------
% 2.16/1.25  #Subsume      : 14
% 2.16/1.25  #Demod        : 18
% 2.16/1.25  #Tautology    : 37
% 2.16/1.25  #SimpNegUnit  : 0
% 2.16/1.25  #BackRed      : 0
% 2.16/1.25  
% 2.16/1.25  #Partial instantiations: 0
% 2.16/1.25  #Strategies tried      : 1
% 2.16/1.25  
% 2.16/1.25  Timing (in seconds)
% 2.16/1.25  ----------------------
% 2.16/1.26  Preprocessing        : 0.29
% 2.16/1.26  Parsing              : 0.16
% 2.16/1.26  CNF conversion       : 0.02
% 2.16/1.26  Main loop            : 0.20
% 2.16/1.26  Inferencing          : 0.08
% 2.16/1.26  Reduction            : 0.07
% 2.16/1.26  Demodulation         : 0.06
% 2.16/1.26  BG Simplification    : 0.01
% 2.16/1.26  Subsumption          : 0.04
% 2.16/1.26  Abstraction          : 0.01
% 2.16/1.26  MUC search           : 0.00
% 2.16/1.26  Cooper               : 0.00
% 2.16/1.26  Total                : 0.52
% 2.16/1.26  Index Insertion      : 0.00
% 2.16/1.26  Index Deletion       : 0.00
% 2.16/1.26  Index Matching       : 0.00
% 2.16/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
