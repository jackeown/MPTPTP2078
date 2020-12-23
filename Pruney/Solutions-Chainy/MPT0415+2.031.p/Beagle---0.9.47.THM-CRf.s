%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:49 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   53 (  78 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 110 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_70,axiom,(
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

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_54,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    ! [B_35] : k3_xboole_0(k1_xboole_0,B_35) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_10])).

tff(c_89,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden(C_39,k3_xboole_0(A_37,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [B_35,C_39] :
      ( ~ r1_xboole_0(k1_xboole_0,B_35)
      | ~ r2_hidden(C_39,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_89])).

tff(c_94,plain,(
    ! [C_39] : ~ r2_hidden(C_39,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_16,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_564,plain,(
    ! [A_84,B_85,C_86] :
      ( r2_hidden('#skF_2'(A_84,B_85,C_86),C_86)
      | r2_hidden(k3_subset_1(A_84,'#skF_2'(A_84,B_85,C_86)),B_85)
      | k7_setfam_1(A_84,B_85) = C_86
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k1_zfmisc_1(A_84)))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_582,plain,(
    ! [A_84,C_86] :
      ( r2_hidden('#skF_2'(A_84,k1_xboole_0,C_86),C_86)
      | k7_setfam_1(A_84,k1_xboole_0) = C_86
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k1_zfmisc_1(A_84)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(resolution,[status(thm)],[c_564,c_94])).

tff(c_594,plain,(
    ! [A_87,C_88] :
      ( r2_hidden('#skF_2'(A_87,k1_xboole_0,C_88),C_88)
      | k7_setfam_1(A_87,k1_xboole_0) = C_88
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k1_zfmisc_1(A_87))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_582])).

tff(c_602,plain,(
    ! [A_87] :
      ( r2_hidden('#skF_2'(A_87,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | k7_setfam_1(A_87,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_594])).

tff(c_612,plain,(
    ! [A_89] : k7_setfam_1(A_89,k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_602])).

tff(c_36,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_153,plain,(
    ! [A_54,B_55] :
      ( k7_setfam_1(A_54,k7_setfam_1(A_54,B_55)) = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_155,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_153])).

tff(c_160,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_155])).

tff(c_618,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_160])).

tff(c_628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_618])).

tff(c_629,plain,(
    ! [B_35] : ~ r1_xboole_0(k1_xboole_0,B_35) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_837,plain,(
    ! [B_123,C_124,A_125] :
      ( r1_xboole_0(B_123,C_124)
      | ~ r1_tarski(B_123,k3_subset_1(A_125,C_124))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(A_125))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_844,plain,(
    ! [C_124,A_125] :
      ( r1_xboole_0(k1_xboole_0,C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(A_125))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_6,c_837])).

tff(c_848,plain,(
    ! [C_124,A_125] :
      ( r1_xboole_0(k1_xboole_0,C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(A_125)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_844])).

tff(c_849,plain,(
    ! [C_124,A_125] : ~ m1_subset_1(C_124,k1_zfmisc_1(A_125)) ),
    inference(negUnitSimplification,[status(thm)],[c_629,c_848])).

tff(c_862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_849,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:14:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.46  
% 2.95/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.46  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.95/1.46  
% 2.95/1.46  %Foreground sorts:
% 2.95/1.46  
% 2.95/1.46  
% 2.95/1.46  %Background operators:
% 2.95/1.46  
% 2.95/1.46  
% 2.95/1.46  %Foreground operators:
% 2.95/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.95/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.46  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.95/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.46  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.95/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.95/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.95/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.95/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.95/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.46  
% 2.95/1.47  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.95/1.47  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.95/1.47  tff(f_45, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.95/1.47  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.95/1.47  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.95/1.47  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.95/1.47  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.95/1.47  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.95/1.47  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.95/1.47  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.95/1.47  tff(c_54, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.95/1.47  tff(c_10, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.95/1.47  tff(c_64, plain, (![B_35]: (k3_xboole_0(k1_xboole_0, B_35)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_10])).
% 2.95/1.47  tff(c_89, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, k3_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.95/1.47  tff(c_92, plain, (![B_35, C_39]: (~r1_xboole_0(k1_xboole_0, B_35) | ~r2_hidden(C_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_64, c_89])).
% 2.95/1.47  tff(c_94, plain, (![C_39]: (~r2_hidden(C_39, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_92])).
% 2.95/1.47  tff(c_16, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.95/1.47  tff(c_564, plain, (![A_84, B_85, C_86]: (r2_hidden('#skF_2'(A_84, B_85, C_86), C_86) | r2_hidden(k3_subset_1(A_84, '#skF_2'(A_84, B_85, C_86)), B_85) | k7_setfam_1(A_84, B_85)=C_86 | ~m1_subset_1(C_86, k1_zfmisc_1(k1_zfmisc_1(A_84))) | ~m1_subset_1(B_85, k1_zfmisc_1(k1_zfmisc_1(A_84))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.95/1.47  tff(c_582, plain, (![A_84, C_86]: (r2_hidden('#skF_2'(A_84, k1_xboole_0, C_86), C_86) | k7_setfam_1(A_84, k1_xboole_0)=C_86 | ~m1_subset_1(C_86, k1_zfmisc_1(k1_zfmisc_1(A_84))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_84))))), inference(resolution, [status(thm)], [c_564, c_94])).
% 2.95/1.47  tff(c_594, plain, (![A_87, C_88]: (r2_hidden('#skF_2'(A_87, k1_xboole_0, C_88), C_88) | k7_setfam_1(A_87, k1_xboole_0)=C_88 | ~m1_subset_1(C_88, k1_zfmisc_1(k1_zfmisc_1(A_87))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_582])).
% 2.95/1.47  tff(c_602, plain, (![A_87]: (r2_hidden('#skF_2'(A_87, k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1(A_87, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_594])).
% 2.95/1.47  tff(c_612, plain, (![A_89]: (k7_setfam_1(A_89, k1_xboole_0)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_94, c_602])).
% 2.95/1.47  tff(c_36, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.95/1.47  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.95/1.47  tff(c_153, plain, (![A_54, B_55]: (k7_setfam_1(A_54, k7_setfam_1(A_54, B_55))=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.95/1.47  tff(c_155, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_40, c_153])).
% 2.95/1.47  tff(c_160, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_155])).
% 2.95/1.47  tff(c_618, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_612, c_160])).
% 2.95/1.47  tff(c_628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_618])).
% 2.95/1.47  tff(c_629, plain, (![B_35]: (~r1_xboole_0(k1_xboole_0, B_35))), inference(splitRight, [status(thm)], [c_92])).
% 2.95/1.47  tff(c_6, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.95/1.47  tff(c_837, plain, (![B_123, C_124, A_125]: (r1_xboole_0(B_123, C_124) | ~r1_tarski(B_123, k3_subset_1(A_125, C_124)) | ~m1_subset_1(C_124, k1_zfmisc_1(A_125)) | ~m1_subset_1(B_123, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.95/1.47  tff(c_844, plain, (![C_124, A_125]: (r1_xboole_0(k1_xboole_0, C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(A_125)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_125)))), inference(resolution, [status(thm)], [c_6, c_837])).
% 2.95/1.47  tff(c_848, plain, (![C_124, A_125]: (r1_xboole_0(k1_xboole_0, C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(A_125)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_844])).
% 2.95/1.47  tff(c_849, plain, (![C_124, A_125]: (~m1_subset_1(C_124, k1_zfmisc_1(A_125)))), inference(negUnitSimplification, [status(thm)], [c_629, c_848])).
% 2.95/1.47  tff(c_862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_849, c_40])).
% 2.95/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.47  
% 2.95/1.47  Inference rules
% 2.95/1.47  ----------------------
% 2.95/1.47  #Ref     : 0
% 2.95/1.47  #Sup     : 191
% 2.95/1.47  #Fact    : 0
% 2.95/1.47  #Define  : 0
% 2.95/1.47  #Split   : 1
% 2.95/1.47  #Chain   : 0
% 2.95/1.47  #Close   : 0
% 2.95/1.47  
% 2.95/1.47  Ordering : KBO
% 2.95/1.47  
% 2.95/1.47  Simplification rules
% 2.95/1.47  ----------------------
% 2.95/1.47  #Subsume      : 15
% 2.95/1.47  #Demod        : 197
% 2.95/1.48  #Tautology    : 123
% 2.95/1.48  #SimpNegUnit  : 13
% 2.95/1.48  #BackRed      : 4
% 2.95/1.48  
% 2.95/1.48  #Partial instantiations: 0
% 2.95/1.48  #Strategies tried      : 1
% 2.95/1.48  
% 2.95/1.48  Timing (in seconds)
% 2.95/1.48  ----------------------
% 2.95/1.48  Preprocessing        : 0.31
% 2.95/1.48  Parsing              : 0.17
% 2.95/1.48  CNF conversion       : 0.02
% 2.95/1.48  Main loop            : 0.34
% 2.95/1.48  Inferencing          : 0.13
% 2.95/1.48  Reduction            : 0.12
% 2.95/1.48  Demodulation         : 0.09
% 2.95/1.48  BG Simplification    : 0.02
% 2.95/1.48  Subsumption          : 0.05
% 2.95/1.48  Abstraction          : 0.02
% 2.95/1.48  MUC search           : 0.00
% 2.95/1.48  Cooper               : 0.00
% 2.95/1.48  Total                : 0.68
% 2.95/1.48  Index Insertion      : 0.00
% 2.95/1.48  Index Deletion       : 0.00
% 2.95/1.48  Index Matching       : 0.00
% 2.95/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
