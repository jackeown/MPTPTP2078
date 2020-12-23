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
% DateTime   : Thu Dec  3 09:55:42 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   49 (  77 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 150 expanded)
%              Number of equality atoms :   26 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_14] : m1_subset_1(k2_subset_1(A_14),k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    ! [A_14] : m1_subset_1(A_14,k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_151,plain,(
    ! [A_45,B_46,C_47] :
      ( k4_subset_1(A_45,B_46,C_47) = k2_xboole_0(B_46,C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_158,plain,(
    ! [A_48,B_49] :
      ( k4_subset_1(A_48,B_49,A_48) = k2_xboole_0(B_49,A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(resolution,[status(thm)],[c_37,c_151])).

tff(c_164,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_158])).

tff(c_34,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_34])).

tff(c_172,plain,(
    k2_xboole_0('#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_38])).

tff(c_360,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden('#skF_1'(A_75,B_76,C_77),B_76)
      | r2_hidden('#skF_1'(A_75,B_76,C_77),A_75)
      | r2_hidden('#skF_2'(A_75,B_76,C_77),C_77)
      | k2_xboole_0(A_75,B_76) = C_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_421,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76,A_75),B_76)
      | r2_hidden('#skF_2'(A_75,B_76,A_75),A_75)
      | k2_xboole_0(A_75,B_76) = A_75 ) ),
    inference(resolution,[status(thm)],[c_360,c_18])).

tff(c_522,plain,(
    ! [A_84,B_85,C_86] :
      ( r2_hidden('#skF_1'(A_84,B_85,C_86),B_85)
      | r2_hidden('#skF_1'(A_84,B_85,C_86),A_84)
      | ~ r2_hidden('#skF_2'(A_84,B_85,C_86),A_84)
      | k2_xboole_0(A_84,B_85) = C_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_753,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_1'(A_96,B_97,A_96),B_97)
      | ~ r2_hidden('#skF_2'(A_96,B_97,A_96),A_96)
      | k2_xboole_0(A_96,B_97) = A_96 ) ),
    inference(resolution,[status(thm)],[c_522,c_14])).

tff(c_767,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_1'(A_98,B_99,A_98),B_99)
      | k2_xboole_0(A_98,B_99) = A_98 ) ),
    inference(resolution,[status(thm)],[c_421,c_753])).

tff(c_30,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_797,plain,(
    ! [A_100,B_101,A_102] :
      ( r2_hidden('#skF_1'(A_100,B_101,A_100),A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_102))
      | k2_xboole_0(A_100,B_101) = A_100 ) ),
    inference(resolution,[status(thm)],[c_767,c_30])).

tff(c_961,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_2'(A_114,B_115,A_114),A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114))
      | k2_xboole_0(A_114,B_115) = A_114 ) ),
    inference(resolution,[status(thm)],[c_797,c_18])).

tff(c_819,plain,(
    ! [A_102,B_101] :
      ( ~ r2_hidden('#skF_2'(A_102,B_101,A_102),A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_102))
      | k2_xboole_0(A_102,B_101) = A_102 ) ),
    inference(resolution,[status(thm)],[c_797,c_14])).

tff(c_1008,plain,(
    ! [B_118,A_119] :
      ( ~ m1_subset_1(B_118,k1_zfmisc_1(A_119))
      | k2_xboole_0(A_119,B_118) = A_119 ) ),
    inference(resolution,[status(thm)],[c_961,c_819])).

tff(c_1017,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_1008])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1037,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_2])).

tff(c_1050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_1037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:07:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.34  
% 2.92/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.34  %$ r2_hidden > m1_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.92/1.34  
% 2.92/1.34  %Foreground sorts:
% 2.92/1.34  
% 2.92/1.34  
% 2.92/1.34  %Background operators:
% 2.92/1.34  
% 2.92/1.34  
% 2.92/1.34  %Foreground operators:
% 2.92/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.92/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.92/1.34  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.92/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.92/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.92/1.34  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.92/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.34  
% 2.92/1.35  tff(f_62, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.92/1.35  tff(f_42, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.92/1.35  tff(f_44, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.92/1.35  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.92/1.35  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.92/1.35  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.92/1.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.92/1.35  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.92/1.35  tff(c_26, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.92/1.35  tff(c_28, plain, (![A_14]: (m1_subset_1(k2_subset_1(A_14), k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.92/1.35  tff(c_37, plain, (![A_14]: (m1_subset_1(A_14, k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 2.92/1.35  tff(c_151, plain, (![A_45, B_46, C_47]: (k4_subset_1(A_45, B_46, C_47)=k2_xboole_0(B_46, C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(A_45)) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.92/1.35  tff(c_158, plain, (![A_48, B_49]: (k4_subset_1(A_48, B_49, A_48)=k2_xboole_0(B_49, A_48) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(resolution, [status(thm)], [c_37, c_151])).
% 2.92/1.35  tff(c_164, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_158])).
% 2.92/1.35  tff(c_34, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.92/1.35  tff(c_38, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_34])).
% 2.92/1.35  tff(c_172, plain, (k2_xboole_0('#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_38])).
% 2.92/1.35  tff(c_360, plain, (![A_75, B_76, C_77]: (r2_hidden('#skF_1'(A_75, B_76, C_77), B_76) | r2_hidden('#skF_1'(A_75, B_76, C_77), A_75) | r2_hidden('#skF_2'(A_75, B_76, C_77), C_77) | k2_xboole_0(A_75, B_76)=C_77)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.92/1.35  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.92/1.35  tff(c_421, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75, B_76, A_75), B_76) | r2_hidden('#skF_2'(A_75, B_76, A_75), A_75) | k2_xboole_0(A_75, B_76)=A_75)), inference(resolution, [status(thm)], [c_360, c_18])).
% 2.92/1.35  tff(c_522, plain, (![A_84, B_85, C_86]: (r2_hidden('#skF_1'(A_84, B_85, C_86), B_85) | r2_hidden('#skF_1'(A_84, B_85, C_86), A_84) | ~r2_hidden('#skF_2'(A_84, B_85, C_86), A_84) | k2_xboole_0(A_84, B_85)=C_86)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.92/1.35  tff(c_14, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.92/1.35  tff(c_753, plain, (![A_96, B_97]: (r2_hidden('#skF_1'(A_96, B_97, A_96), B_97) | ~r2_hidden('#skF_2'(A_96, B_97, A_96), A_96) | k2_xboole_0(A_96, B_97)=A_96)), inference(resolution, [status(thm)], [c_522, c_14])).
% 2.92/1.35  tff(c_767, plain, (![A_98, B_99]: (r2_hidden('#skF_1'(A_98, B_99, A_98), B_99) | k2_xboole_0(A_98, B_99)=A_98)), inference(resolution, [status(thm)], [c_421, c_753])).
% 2.92/1.35  tff(c_30, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.92/1.35  tff(c_797, plain, (![A_100, B_101, A_102]: (r2_hidden('#skF_1'(A_100, B_101, A_100), A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_102)) | k2_xboole_0(A_100, B_101)=A_100)), inference(resolution, [status(thm)], [c_767, c_30])).
% 2.92/1.35  tff(c_961, plain, (![A_114, B_115]: (r2_hidden('#skF_2'(A_114, B_115, A_114), A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)) | k2_xboole_0(A_114, B_115)=A_114)), inference(resolution, [status(thm)], [c_797, c_18])).
% 2.92/1.35  tff(c_819, plain, (![A_102, B_101]: (~r2_hidden('#skF_2'(A_102, B_101, A_102), A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_102)) | k2_xboole_0(A_102, B_101)=A_102)), inference(resolution, [status(thm)], [c_797, c_14])).
% 2.92/1.35  tff(c_1008, plain, (![B_118, A_119]: (~m1_subset_1(B_118, k1_zfmisc_1(A_119)) | k2_xboole_0(A_119, B_118)=A_119)), inference(resolution, [status(thm)], [c_961, c_819])).
% 2.92/1.35  tff(c_1017, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_36, c_1008])).
% 2.92/1.35  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.92/1.35  tff(c_1037, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1017, c_2])).
% 2.92/1.35  tff(c_1050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_1037])).
% 2.92/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.35  
% 2.92/1.35  Inference rules
% 2.92/1.35  ----------------------
% 2.92/1.35  #Ref     : 0
% 2.92/1.35  #Sup     : 219
% 2.92/1.35  #Fact    : 6
% 2.92/1.35  #Define  : 0
% 2.92/1.35  #Split   : 0
% 2.92/1.35  #Chain   : 0
% 2.92/1.35  #Close   : 0
% 2.92/1.35  
% 2.92/1.36  Ordering : KBO
% 2.92/1.36  
% 2.92/1.36  Simplification rules
% 2.92/1.36  ----------------------
% 2.92/1.36  #Subsume      : 42
% 2.92/1.36  #Demod        : 37
% 2.92/1.36  #Tautology    : 65
% 2.92/1.36  #SimpNegUnit  : 1
% 2.92/1.36  #BackRed      : 4
% 2.92/1.36  
% 2.92/1.36  #Partial instantiations: 0
% 2.92/1.36  #Strategies tried      : 1
% 2.92/1.36  
% 2.92/1.36  Timing (in seconds)
% 2.92/1.36  ----------------------
% 2.92/1.36  Preprocessing        : 0.28
% 2.92/1.36  Parsing              : 0.14
% 2.92/1.36  CNF conversion       : 0.02
% 2.92/1.36  Main loop            : 0.42
% 2.92/1.36  Inferencing          : 0.15
% 2.92/1.36  Reduction            : 0.12
% 3.14/1.36  Demodulation         : 0.09
% 3.14/1.36  BG Simplification    : 0.02
% 3.14/1.36  Subsumption          : 0.10
% 3.14/1.36  Abstraction          : 0.03
% 3.14/1.36  MUC search           : 0.00
% 3.14/1.36  Cooper               : 0.00
% 3.14/1.36  Total                : 0.72
% 3.14/1.36  Index Insertion      : 0.00
% 3.14/1.36  Index Deletion       : 0.00
% 3.14/1.36  Index Matching       : 0.00
% 3.14/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
