%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:06 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 108 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 225 expanded)
%              Number of equality atoms :   21 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( k3_subset_1(A,B) = k3_subset_1(A,C)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_subset_1)).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(c_22,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_tarski(A_25,B_26)
      | ~ r1_xboole_0(A_25,C_27)
      | ~ r1_tarski(A_25,k2_xboole_0(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_63,plain,(
    ! [A_31,B_32,C_33] :
      ( r1_tarski(A_31,B_32)
      | ~ r1_xboole_0(A_31,C_33)
      | k4_xboole_0(A_31,k2_xboole_0(B_32,C_33)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_47])).

tff(c_68,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,A_34)
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_63])).

tff(c_71,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(resolution,[status(thm)],[c_14,c_68])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    k3_subset_1('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_242,plain,(
    ! [B_59,C_60,A_61] :
      ( r1_tarski(B_59,C_60)
      | ~ r1_tarski(k3_subset_1(A_61,C_60),k3_subset_1(A_61,B_59))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_252,plain,(
    ! [B_59] :
      ( r1_tarski(B_59,'#skF_3')
      | ~ r1_tarski(k3_subset_1('#skF_2','#skF_4'),k3_subset_1('#skF_2',B_59))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_59,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_242])).

tff(c_312,plain,(
    ! [B_65] :
      ( r1_tarski(B_65,'#skF_3')
      | ~ r1_tarski(k3_subset_1('#skF_2','#skF_4'),k3_subset_1('#skF_2',B_65))
      | ~ m1_subset_1(B_65,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_252])).

tff(c_316,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_312])).

tff(c_325,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_316])).

tff(c_6,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski('#skF_1'(A_1,B_2,C_3),B_2)
      | k3_xboole_0(B_2,C_3) = A_1
      | ~ r1_tarski(A_1,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_100,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_tarski('#skF_1'(A_40,B_41,C_42),A_40)
      | k3_xboole_0(B_41,C_42) = A_40
      | ~ r1_tarski(A_40,C_42)
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_104,plain,(
    ! [B_2,C_3] :
      ( k3_xboole_0(B_2,C_3) = B_2
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(B_2,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_111,plain,(
    ! [B_2,C_3] :
      ( k3_xboole_0(B_2,C_3) = B_2
      | ~ r1_tarski(B_2,C_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_104])).

tff(c_339,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_325,c_111])).

tff(c_364,plain,(
    ! [A_66,C_67,B_68] :
      ( r1_tarski(k3_subset_1(A_66,C_67),k3_subset_1(A_66,B_68))
      | ~ r1_tarski(B_68,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_383,plain,(
    ! [B_68] :
      ( r1_tarski(k3_subset_1('#skF_2','#skF_4'),k3_subset_1('#skF_2',B_68))
      | ~ r1_tarski(B_68,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_68,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_364])).

tff(c_411,plain,(
    ! [B_70] :
      ( r1_tarski(k3_subset_1('#skF_2','#skF_4'),k3_subset_1('#skF_2',B_70))
      | ~ r1_tarski(B_70,'#skF_3')
      | ~ m1_subset_1(B_70,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_383])).

tff(c_18,plain,(
    ! [B_14,C_16,A_13] :
      ( r1_tarski(B_14,C_16)
      | ~ r1_tarski(k3_subset_1(A_13,C_16),k3_subset_1(A_13,B_14))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_417,plain,(
    ! [B_70] :
      ( r1_tarski(B_70,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski(B_70,'#skF_3')
      | ~ m1_subset_1(B_70,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_411,c_18])).

tff(c_439,plain,(
    ! [B_71] :
      ( r1_tarski(B_71,'#skF_4')
      | ~ r1_tarski(B_71,'#skF_3')
      | ~ m1_subset_1(B_71,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_417])).

tff(c_445,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_439])).

tff(c_451,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_445])).

tff(c_152,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski('#skF_1'(A_47,B_48,C_49),C_49)
      | k3_xboole_0(B_48,C_49) = A_47
      | ~ r1_tarski(A_47,C_49)
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r1_tarski('#skF_1'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(B_2,C_3) = A_1
      | ~ r1_tarski(A_1,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_159,plain,(
    ! [B_48,C_49] :
      ( k3_xboole_0(B_48,C_49) = C_49
      | ~ r1_tarski(C_49,C_49)
      | ~ r1_tarski(C_49,B_48) ) ),
    inference(resolution,[status(thm)],[c_152,c_2])).

tff(c_170,plain,(
    ! [B_48,C_49] :
      ( k3_xboole_0(B_48,C_49) = C_49
      | ~ r1_tarski(C_49,B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_159])).

tff(c_454,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_451,c_170])).

tff(c_462,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_454])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:34:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.39  
% 2.19/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.39  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.19/1.39  
% 2.19/1.39  %Foreground sorts:
% 2.19/1.39  
% 2.19/1.39  
% 2.19/1.39  %Background operators:
% 2.19/1.39  
% 2.19/1.39  
% 2.19/1.39  %Foreground operators:
% 2.19/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.19/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.19/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.39  
% 2.48/1.41  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((k3_subset_1(A, B) = k3_subset_1(A, C)) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_subset_1)).
% 2.48/1.41  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.48/1.41  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.48/1.41  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.48/1.41  tff(f_52, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 2.48/1.41  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.48/1.41  tff(f_38, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 2.48/1.41  tff(c_22, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.48/1.41  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.48/1.41  tff(c_14, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.48/1.41  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.48/1.41  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.48/1.41  tff(c_47, plain, (![A_25, B_26, C_27]: (r1_tarski(A_25, B_26) | ~r1_xboole_0(A_25, C_27) | ~r1_tarski(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.48/1.41  tff(c_63, plain, (![A_31, B_32, C_33]: (r1_tarski(A_31, B_32) | ~r1_xboole_0(A_31, C_33) | k4_xboole_0(A_31, k2_xboole_0(B_32, C_33))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_47])).
% 2.48/1.41  tff(c_68, plain, (![A_34, B_35]: (r1_tarski(A_34, A_34) | ~r1_xboole_0(A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_12, c_63])).
% 2.48/1.41  tff(c_71, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(resolution, [status(thm)], [c_14, c_68])).
% 2.48/1.41  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.48/1.41  tff(c_24, plain, (k3_subset_1('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.48/1.41  tff(c_242, plain, (![B_59, C_60, A_61]: (r1_tarski(B_59, C_60) | ~r1_tarski(k3_subset_1(A_61, C_60), k3_subset_1(A_61, B_59)) | ~m1_subset_1(C_60, k1_zfmisc_1(A_61)) | ~m1_subset_1(B_59, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.48/1.41  tff(c_252, plain, (![B_59]: (r1_tarski(B_59, '#skF_3') | ~r1_tarski(k3_subset_1('#skF_2', '#skF_4'), k3_subset_1('#skF_2', B_59)) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_59, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_242])).
% 2.48/1.41  tff(c_312, plain, (![B_65]: (r1_tarski(B_65, '#skF_3') | ~r1_tarski(k3_subset_1('#skF_2', '#skF_4'), k3_subset_1('#skF_2', B_65)) | ~m1_subset_1(B_65, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_252])).
% 2.48/1.41  tff(c_316, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_71, c_312])).
% 2.48/1.41  tff(c_325, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_316])).
% 2.48/1.41  tff(c_6, plain, (![A_1, B_2, C_3]: (r1_tarski('#skF_1'(A_1, B_2, C_3), B_2) | k3_xboole_0(B_2, C_3)=A_1 | ~r1_tarski(A_1, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.41  tff(c_100, plain, (![A_40, B_41, C_42]: (~r1_tarski('#skF_1'(A_40, B_41, C_42), A_40) | k3_xboole_0(B_41, C_42)=A_40 | ~r1_tarski(A_40, C_42) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.41  tff(c_104, plain, (![B_2, C_3]: (k3_xboole_0(B_2, C_3)=B_2 | ~r1_tarski(B_2, C_3) | ~r1_tarski(B_2, B_2))), inference(resolution, [status(thm)], [c_6, c_100])).
% 2.48/1.41  tff(c_111, plain, (![B_2, C_3]: (k3_xboole_0(B_2, C_3)=B_2 | ~r1_tarski(B_2, C_3))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_104])).
% 2.48/1.41  tff(c_339, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_325, c_111])).
% 2.48/1.41  tff(c_364, plain, (![A_66, C_67, B_68]: (r1_tarski(k3_subset_1(A_66, C_67), k3_subset_1(A_66, B_68)) | ~r1_tarski(B_68, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(A_66)) | ~m1_subset_1(B_68, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.48/1.41  tff(c_383, plain, (![B_68]: (r1_tarski(k3_subset_1('#skF_2', '#skF_4'), k3_subset_1('#skF_2', B_68)) | ~r1_tarski(B_68, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_68, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_364])).
% 2.48/1.41  tff(c_411, plain, (![B_70]: (r1_tarski(k3_subset_1('#skF_2', '#skF_4'), k3_subset_1('#skF_2', B_70)) | ~r1_tarski(B_70, '#skF_3') | ~m1_subset_1(B_70, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_383])).
% 2.48/1.41  tff(c_18, plain, (![B_14, C_16, A_13]: (r1_tarski(B_14, C_16) | ~r1_tarski(k3_subset_1(A_13, C_16), k3_subset_1(A_13, B_14)) | ~m1_subset_1(C_16, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.48/1.41  tff(c_417, plain, (![B_70]: (r1_tarski(B_70, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~r1_tarski(B_70, '#skF_3') | ~m1_subset_1(B_70, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_411, c_18])).
% 2.48/1.41  tff(c_439, plain, (![B_71]: (r1_tarski(B_71, '#skF_4') | ~r1_tarski(B_71, '#skF_3') | ~m1_subset_1(B_71, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_417])).
% 2.48/1.41  tff(c_445, plain, (r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_439])).
% 2.48/1.41  tff(c_451, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_445])).
% 2.48/1.41  tff(c_152, plain, (![A_47, B_48, C_49]: (r1_tarski('#skF_1'(A_47, B_48, C_49), C_49) | k3_xboole_0(B_48, C_49)=A_47 | ~r1_tarski(A_47, C_49) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.41  tff(c_2, plain, (![A_1, B_2, C_3]: (~r1_tarski('#skF_1'(A_1, B_2, C_3), A_1) | k3_xboole_0(B_2, C_3)=A_1 | ~r1_tarski(A_1, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.41  tff(c_159, plain, (![B_48, C_49]: (k3_xboole_0(B_48, C_49)=C_49 | ~r1_tarski(C_49, C_49) | ~r1_tarski(C_49, B_48))), inference(resolution, [status(thm)], [c_152, c_2])).
% 2.48/1.41  tff(c_170, plain, (![B_48, C_49]: (k3_xboole_0(B_48, C_49)=C_49 | ~r1_tarski(C_49, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_159])).
% 2.48/1.41  tff(c_454, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_451, c_170])).
% 2.48/1.41  tff(c_462, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_339, c_454])).
% 2.48/1.41  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_462])).
% 2.48/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.41  
% 2.48/1.41  Inference rules
% 2.48/1.41  ----------------------
% 2.48/1.41  #Ref     : 0
% 2.48/1.41  #Sup     : 94
% 2.48/1.41  #Fact    : 0
% 2.48/1.41  #Define  : 0
% 2.48/1.41  #Split   : 0
% 2.48/1.41  #Chain   : 0
% 2.48/1.41  #Close   : 0
% 2.48/1.41  
% 2.48/1.41  Ordering : KBO
% 2.48/1.41  
% 2.48/1.41  Simplification rules
% 2.48/1.41  ----------------------
% 2.48/1.41  #Subsume      : 2
% 2.48/1.41  #Demod        : 50
% 2.48/1.41  #Tautology    : 47
% 2.48/1.41  #SimpNegUnit  : 1
% 2.48/1.41  #BackRed      : 2
% 2.48/1.41  
% 2.48/1.41  #Partial instantiations: 0
% 2.48/1.41  #Strategies tried      : 1
% 2.48/1.41  
% 2.48/1.41  Timing (in seconds)
% 2.48/1.41  ----------------------
% 2.48/1.41  Preprocessing        : 0.31
% 2.48/1.41  Parsing              : 0.16
% 2.48/1.41  CNF conversion       : 0.02
% 2.48/1.41  Main loop            : 0.25
% 2.48/1.41  Inferencing          : 0.10
% 2.48/1.41  Reduction            : 0.07
% 2.48/1.41  Demodulation         : 0.05
% 2.48/1.41  BG Simplification    : 0.02
% 2.48/1.41  Subsumption          : 0.05
% 2.48/1.41  Abstraction          : 0.01
% 2.48/1.41  MUC search           : 0.00
% 2.48/1.41  Cooper               : 0.00
% 2.48/1.41  Total                : 0.59
% 2.48/1.41  Index Insertion      : 0.00
% 2.48/1.41  Index Deletion       : 0.00
% 2.48/1.41  Index Matching       : 0.00
% 2.48/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
