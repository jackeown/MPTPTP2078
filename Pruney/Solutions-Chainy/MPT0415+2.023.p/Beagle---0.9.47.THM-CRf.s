%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:48 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   57 (  86 expanded)
%              Number of leaves         :   30 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 126 expanded)
%              Number of equality atoms :   23 (  51 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_133,plain,(
    ! [A_57,C_58,B_59] :
      ( m1_subset_1(A_57,C_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_58))
      | ~ r2_hidden(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_138,plain,(
    ! [A_57] :
      ( m1_subset_1(A_57,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_133])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_95,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_95])).

tff(c_108,plain,(
    ! [A_49] : k4_xboole_0(A_49,A_49) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_104])).

tff(c_16,plain,(
    ! [C_14,B_13] : ~ r2_hidden(C_14,k4_xboole_0(B_13,k1_tarski(C_14))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_113,plain,(
    ! [C_14] : ~ r2_hidden(C_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_16])).

tff(c_20,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_169,plain,(
    ! [A_71,B_72] :
      ( k7_setfam_1(A_71,k7_setfam_1(A_71,B_72)) = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(A_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_171,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_169])).

tff(c_176,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_171])).

tff(c_287,plain,(
    ! [A_97,D_98,B_99] :
      ( r2_hidden(k3_subset_1(A_97,D_98),B_99)
      | ~ r2_hidden(D_98,k7_setfam_1(A_97,B_99))
      | ~ m1_subset_1(D_98,k1_zfmisc_1(A_97))
      | ~ m1_subset_1(k7_setfam_1(A_97,B_99),k1_zfmisc_1(k1_zfmisc_1(A_97)))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k1_zfmisc_1(A_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_291,plain,(
    ! [D_98] :
      ( r2_hidden(k3_subset_1('#skF_3',D_98),k1_xboole_0)
      | ~ r2_hidden(D_98,k7_setfam_1('#skF_3',k1_xboole_0))
      | ~ m1_subset_1(D_98,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_287])).

tff(c_297,plain,(
    ! [D_98] :
      ( r2_hidden(k3_subset_1('#skF_3',D_98),k1_xboole_0)
      | ~ r2_hidden(D_98,'#skF_4')
      | ~ m1_subset_1(D_98,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_54,c_176,c_291])).

tff(c_301,plain,(
    ! [D_100] :
      ( ~ r2_hidden(D_100,'#skF_4')
      | ~ m1_subset_1(D_100,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_297])).

tff(c_319,plain,(
    ! [A_57] : ~ r2_hidden(A_57,'#skF_4') ),
    inference(resolution,[status(thm)],[c_138,c_301])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_216,plain,(
    ! [A_91,B_92,C_93] :
      ( r2_hidden('#skF_2'(A_91,B_92,C_93),B_92)
      | r2_hidden('#skF_2'(A_91,B_92,C_93),C_93)
      | C_93 = B_92
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k1_zfmisc_1(A_91)))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_227,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_2'(A_91,B_92,k1_xboole_0),B_92)
      | r2_hidden('#skF_2'(A_91,B_92,k1_xboole_0),k1_xboole_0)
      | k1_xboole_0 = B_92
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(resolution,[status(thm)],[c_20,c_216])).

tff(c_263,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_2'(A_95,B_96,k1_xboole_0),B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k1_zfmisc_1(A_95))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_227])).

tff(c_271,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4',k1_xboole_0),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_263])).

tff(c_279,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4',k1_xboole_0),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_271])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.35  
% 2.42/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.35  %$ r2_hidden > m1_subset_1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.42/1.35  
% 2.42/1.35  %Foreground sorts:
% 2.42/1.35  
% 2.42/1.35  
% 2.42/1.35  %Background operators:
% 2.42/1.35  
% 2.42/1.35  
% 2.42/1.35  %Foreground operators:
% 2.42/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.42/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.35  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.42/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.42/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.42/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.42/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.42/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.42/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.35  
% 2.42/1.37  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.42/1.37  tff(f_84, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.42/1.37  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.42/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.42/1.37  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.42/1.37  tff(f_44, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.42/1.37  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.42/1.37  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.42/1.37  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.42/1.37  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_setfam_1)).
% 2.42/1.37  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.42/1.37  tff(c_133, plain, (![A_57, C_58, B_59]: (m1_subset_1(A_57, C_58) | ~m1_subset_1(B_59, k1_zfmisc_1(C_58)) | ~r2_hidden(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.42/1.37  tff(c_138, plain, (![A_57]: (m1_subset_1(A_57, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_133])).
% 2.42/1.37  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.37  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.42/1.37  tff(c_95, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.42/1.37  tff(c_104, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_95])).
% 2.42/1.37  tff(c_108, plain, (![A_49]: (k4_xboole_0(A_49, A_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_104])).
% 2.42/1.37  tff(c_16, plain, (![C_14, B_13]: (~r2_hidden(C_14, k4_xboole_0(B_13, k1_tarski(C_14))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.42/1.37  tff(c_113, plain, (![C_14]: (~r2_hidden(C_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_108, c_16])).
% 2.42/1.37  tff(c_20, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.42/1.37  tff(c_50, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.42/1.37  tff(c_169, plain, (![A_71, B_72]: (k7_setfam_1(A_71, k7_setfam_1(A_71, B_72))=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(A_71))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.42/1.37  tff(c_171, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_54, c_169])).
% 2.42/1.37  tff(c_176, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_171])).
% 2.42/1.37  tff(c_287, plain, (![A_97, D_98, B_99]: (r2_hidden(k3_subset_1(A_97, D_98), B_99) | ~r2_hidden(D_98, k7_setfam_1(A_97, B_99)) | ~m1_subset_1(D_98, k1_zfmisc_1(A_97)) | ~m1_subset_1(k7_setfam_1(A_97, B_99), k1_zfmisc_1(k1_zfmisc_1(A_97))) | ~m1_subset_1(B_99, k1_zfmisc_1(k1_zfmisc_1(A_97))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.42/1.37  tff(c_291, plain, (![D_98]: (r2_hidden(k3_subset_1('#skF_3', D_98), k1_xboole_0) | ~r2_hidden(D_98, k7_setfam_1('#skF_3', k1_xboole_0)) | ~m1_subset_1(D_98, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_176, c_287])).
% 2.42/1.37  tff(c_297, plain, (![D_98]: (r2_hidden(k3_subset_1('#skF_3', D_98), k1_xboole_0) | ~r2_hidden(D_98, '#skF_4') | ~m1_subset_1(D_98, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_54, c_176, c_291])).
% 2.42/1.37  tff(c_301, plain, (![D_100]: (~r2_hidden(D_100, '#skF_4') | ~m1_subset_1(D_100, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_113, c_297])).
% 2.42/1.37  tff(c_319, plain, (![A_57]: (~r2_hidden(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_138, c_301])).
% 2.42/1.37  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.42/1.37  tff(c_216, plain, (![A_91, B_92, C_93]: (r2_hidden('#skF_2'(A_91, B_92, C_93), B_92) | r2_hidden('#skF_2'(A_91, B_92, C_93), C_93) | C_93=B_92 | ~m1_subset_1(C_93, k1_zfmisc_1(k1_zfmisc_1(A_91))) | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.42/1.37  tff(c_227, plain, (![A_91, B_92]: (r2_hidden('#skF_2'(A_91, B_92, k1_xboole_0), B_92) | r2_hidden('#skF_2'(A_91, B_92, k1_xboole_0), k1_xboole_0) | k1_xboole_0=B_92 | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(resolution, [status(thm)], [c_20, c_216])).
% 2.42/1.37  tff(c_263, plain, (![A_95, B_96]: (r2_hidden('#skF_2'(A_95, B_96, k1_xboole_0), B_96) | k1_xboole_0=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(k1_zfmisc_1(A_95))))), inference(negUnitSimplification, [status(thm)], [c_113, c_227])).
% 2.42/1.37  tff(c_271, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', k1_xboole_0), '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_54, c_263])).
% 2.42/1.37  tff(c_279, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', k1_xboole_0), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_271])).
% 2.42/1.37  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_319, c_279])).
% 2.42/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.37  
% 2.42/1.37  Inference rules
% 2.42/1.37  ----------------------
% 2.42/1.37  #Ref     : 0
% 2.42/1.37  #Sup     : 61
% 2.42/1.37  #Fact    : 0
% 2.42/1.37  #Define  : 0
% 2.42/1.37  #Split   : 1
% 2.42/1.37  #Chain   : 0
% 2.42/1.37  #Close   : 0
% 2.42/1.37  
% 2.42/1.37  Ordering : KBO
% 2.42/1.37  
% 2.42/1.37  Simplification rules
% 2.42/1.37  ----------------------
% 2.42/1.37  #Subsume      : 12
% 2.42/1.37  #Demod        : 13
% 2.42/1.37  #Tautology    : 29
% 2.42/1.37  #SimpNegUnit  : 10
% 2.42/1.37  #BackRed      : 3
% 2.42/1.37  
% 2.42/1.37  #Partial instantiations: 0
% 2.42/1.37  #Strategies tried      : 1
% 2.42/1.37  
% 2.42/1.37  Timing (in seconds)
% 2.42/1.37  ----------------------
% 2.42/1.37  Preprocessing        : 0.30
% 2.42/1.37  Parsing              : 0.15
% 2.42/1.37  CNF conversion       : 0.02
% 2.42/1.37  Main loop            : 0.22
% 2.42/1.37  Inferencing          : 0.08
% 2.42/1.37  Reduction            : 0.06
% 2.42/1.37  Demodulation         : 0.04
% 2.42/1.37  BG Simplification    : 0.02
% 2.42/1.37  Subsumption          : 0.05
% 2.42/1.37  Abstraction          : 0.01
% 2.42/1.37  MUC search           : 0.00
% 2.42/1.37  Cooper               : 0.00
% 2.42/1.37  Total                : 0.56
% 2.42/1.37  Index Insertion      : 0.00
% 2.42/1.37  Index Deletion       : 0.00
% 2.42/1.37  Index Matching       : 0.00
% 2.42/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
