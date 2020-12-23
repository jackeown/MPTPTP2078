%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:52 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   46 (  74 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 ( 132 expanded)
%              Number of equality atoms :   12 (  27 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_38,c_40])).

tff(c_49,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_53,plain,(
    k3_xboole_0('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_48,c_49])).

tff(c_58,plain,(
    ! [D_30,B_31,A_32] :
      ( r2_hidden(D_30,B_31)
      | ~ r2_hidden(D_30,k3_xboole_0(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_61,plain,(
    ! [D_30] :
      ( r2_hidden(D_30,k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(D_30,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_58])).

tff(c_103,plain,(
    ! [A_58,B_59,C_60] :
      ( k4_tarski('#skF_3'(A_58,B_59,C_60),'#skF_4'(A_58,B_59,C_60)) = A_58
      | ~ r2_hidden(A_58,k2_zfmisc_1(B_59,C_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,(
    ! [A_45,C_46,B_47,D_48] :
      ( r2_hidden(A_45,C_46)
      | ~ r2_hidden(k4_tarski(A_45,B_47),k2_zfmisc_1(C_46,D_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_80,plain,(
    ! [A_45,B_47] :
      ( r2_hidden(A_45,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_45,B_47),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_61,c_75])).

tff(c_112,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden('#skF_3'(A_58,B_59,C_60),'#skF_6')
      | ~ r2_hidden(A_58,'#skF_8')
      | ~ r2_hidden(A_58,k2_zfmisc_1(B_59,C_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_80])).

tff(c_22,plain,(
    ! [A_9,B_10,C_11] :
      ( k4_tarski('#skF_3'(A_9,B_10,C_11),'#skF_4'(A_9,B_10,C_11)) = A_9
      | ~ r2_hidden(A_9,k2_zfmisc_1(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_68,plain,(
    ! [B_39,D_40,A_41,C_42] :
      ( r2_hidden(B_39,D_40)
      | ~ r2_hidden(k4_tarski(A_41,B_39),k2_zfmisc_1(C_42,D_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_73,plain,(
    ! [B_39,A_41] :
      ( r2_hidden(B_39,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_41,B_39),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_61,c_68])).

tff(c_128,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden('#skF_4'(A_64,B_65,C_66),'#skF_7')
      | ~ r2_hidden(A_64,'#skF_8')
      | ~ r2_hidden(A_64,k2_zfmisc_1(B_65,C_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_73])).

tff(c_34,plain,(
    ! [F_23,E_22] :
      ( ~ r2_hidden(F_23,'#skF_7')
      | ~ r2_hidden(E_22,'#skF_6')
      | k4_tarski(E_22,F_23) != '#skF_5' ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_289,plain,(
    ! [E_92,A_93,B_94,C_95] :
      ( ~ r2_hidden(E_92,'#skF_6')
      | k4_tarski(E_92,'#skF_4'(A_93,B_94,C_95)) != '#skF_5'
      | ~ r2_hidden(A_93,'#skF_8')
      | ~ r2_hidden(A_93,k2_zfmisc_1(B_94,C_95)) ) ),
    inference(resolution,[status(thm)],[c_128,c_34])).

tff(c_1480,plain,(
    ! [A_211,B_212,C_213] :
      ( ~ r2_hidden('#skF_3'(A_211,B_212,C_213),'#skF_6')
      | A_211 != '#skF_5'
      | ~ r2_hidden(A_211,'#skF_8')
      | ~ r2_hidden(A_211,k2_zfmisc_1(B_212,C_213))
      | ~ r2_hidden(A_211,k2_zfmisc_1(B_212,C_213)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_289])).

tff(c_1523,plain,(
    ! [A_219,B_220,C_221] :
      ( A_219 != '#skF_5'
      | ~ r2_hidden(A_219,'#skF_8')
      | ~ r2_hidden(A_219,k2_zfmisc_1(B_220,C_221)) ) ),
    inference(resolution,[status(thm)],[c_112,c_1480])).

tff(c_1647,plain,(
    ~ r2_hidden('#skF_5','#skF_8') ),
    inference(resolution,[status(thm)],[c_61,c_1523])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1647,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:55:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.70  
% 4.09/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.71  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 4.09/1.71  
% 4.09/1.71  %Foreground sorts:
% 4.09/1.71  
% 4.09/1.71  
% 4.09/1.71  %Background operators:
% 4.09/1.71  
% 4.09/1.71  
% 4.09/1.71  %Foreground operators:
% 4.09/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.09/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.09/1.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.09/1.71  tff('#skF_7', type, '#skF_7': $i).
% 4.09/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.09/1.71  tff('#skF_6', type, '#skF_6': $i).
% 4.09/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.09/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.09/1.71  tff('#skF_8', type, '#skF_8': $i).
% 4.09/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.09/1.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.09/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.09/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.09/1.71  
% 4.09/1.72  tff(f_69, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 4.09/1.72  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.09/1.72  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.09/1.72  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.09/1.72  tff(f_45, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 4.09/1.72  tff(f_51, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.09/1.72  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.09/1.72  tff(c_40, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.09/1.72  tff(c_48, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_38, c_40])).
% 4.09/1.72  tff(c_49, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.09/1.72  tff(c_53, plain, (k3_xboole_0('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))='#skF_8'), inference(resolution, [status(thm)], [c_48, c_49])).
% 4.09/1.72  tff(c_58, plain, (![D_30, B_31, A_32]: (r2_hidden(D_30, B_31) | ~r2_hidden(D_30, k3_xboole_0(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.09/1.72  tff(c_61, plain, (![D_30]: (r2_hidden(D_30, k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(D_30, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_58])).
% 4.09/1.72  tff(c_103, plain, (![A_58, B_59, C_60]: (k4_tarski('#skF_3'(A_58, B_59, C_60), '#skF_4'(A_58, B_59, C_60))=A_58 | ~r2_hidden(A_58, k2_zfmisc_1(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.09/1.72  tff(c_75, plain, (![A_45, C_46, B_47, D_48]: (r2_hidden(A_45, C_46) | ~r2_hidden(k4_tarski(A_45, B_47), k2_zfmisc_1(C_46, D_48)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.09/1.72  tff(c_80, plain, (![A_45, B_47]: (r2_hidden(A_45, '#skF_6') | ~r2_hidden(k4_tarski(A_45, B_47), '#skF_8'))), inference(resolution, [status(thm)], [c_61, c_75])).
% 4.09/1.72  tff(c_112, plain, (![A_58, B_59, C_60]: (r2_hidden('#skF_3'(A_58, B_59, C_60), '#skF_6') | ~r2_hidden(A_58, '#skF_8') | ~r2_hidden(A_58, k2_zfmisc_1(B_59, C_60)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_80])).
% 4.09/1.72  tff(c_22, plain, (![A_9, B_10, C_11]: (k4_tarski('#skF_3'(A_9, B_10, C_11), '#skF_4'(A_9, B_10, C_11))=A_9 | ~r2_hidden(A_9, k2_zfmisc_1(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.09/1.72  tff(c_68, plain, (![B_39, D_40, A_41, C_42]: (r2_hidden(B_39, D_40) | ~r2_hidden(k4_tarski(A_41, B_39), k2_zfmisc_1(C_42, D_40)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.09/1.72  tff(c_73, plain, (![B_39, A_41]: (r2_hidden(B_39, '#skF_7') | ~r2_hidden(k4_tarski(A_41, B_39), '#skF_8'))), inference(resolution, [status(thm)], [c_61, c_68])).
% 4.09/1.72  tff(c_128, plain, (![A_64, B_65, C_66]: (r2_hidden('#skF_4'(A_64, B_65, C_66), '#skF_7') | ~r2_hidden(A_64, '#skF_8') | ~r2_hidden(A_64, k2_zfmisc_1(B_65, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_73])).
% 4.09/1.72  tff(c_34, plain, (![F_23, E_22]: (~r2_hidden(F_23, '#skF_7') | ~r2_hidden(E_22, '#skF_6') | k4_tarski(E_22, F_23)!='#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.09/1.72  tff(c_289, plain, (![E_92, A_93, B_94, C_95]: (~r2_hidden(E_92, '#skF_6') | k4_tarski(E_92, '#skF_4'(A_93, B_94, C_95))!='#skF_5' | ~r2_hidden(A_93, '#skF_8') | ~r2_hidden(A_93, k2_zfmisc_1(B_94, C_95)))), inference(resolution, [status(thm)], [c_128, c_34])).
% 4.09/1.72  tff(c_1480, plain, (![A_211, B_212, C_213]: (~r2_hidden('#skF_3'(A_211, B_212, C_213), '#skF_6') | A_211!='#skF_5' | ~r2_hidden(A_211, '#skF_8') | ~r2_hidden(A_211, k2_zfmisc_1(B_212, C_213)) | ~r2_hidden(A_211, k2_zfmisc_1(B_212, C_213)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_289])).
% 4.09/1.72  tff(c_1523, plain, (![A_219, B_220, C_221]: (A_219!='#skF_5' | ~r2_hidden(A_219, '#skF_8') | ~r2_hidden(A_219, k2_zfmisc_1(B_220, C_221)))), inference(resolution, [status(thm)], [c_112, c_1480])).
% 4.09/1.72  tff(c_1647, plain, (~r2_hidden('#skF_5', '#skF_8')), inference(resolution, [status(thm)], [c_61, c_1523])).
% 4.09/1.72  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.09/1.72  tff(c_1649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1647, c_36])).
% 4.09/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.72  
% 4.09/1.72  Inference rules
% 4.09/1.72  ----------------------
% 4.09/1.72  #Ref     : 0
% 4.09/1.72  #Sup     : 393
% 4.09/1.72  #Fact    : 0
% 4.09/1.72  #Define  : 0
% 4.09/1.72  #Split   : 0
% 4.09/1.72  #Chain   : 0
% 4.09/1.72  #Close   : 0
% 4.09/1.72  
% 4.09/1.72  Ordering : KBO
% 4.09/1.72  
% 4.09/1.72  Simplification rules
% 4.09/1.72  ----------------------
% 4.09/1.72  #Subsume      : 54
% 4.09/1.72  #Demod        : 78
% 4.09/1.72  #Tautology    : 20
% 4.09/1.72  #SimpNegUnit  : 1
% 4.09/1.72  #BackRed      : 1
% 4.09/1.72  
% 4.09/1.72  #Partial instantiations: 0
% 4.09/1.72  #Strategies tried      : 1
% 4.09/1.72  
% 4.09/1.72  Timing (in seconds)
% 4.09/1.72  ----------------------
% 4.09/1.72  Preprocessing        : 0.29
% 4.09/1.72  Parsing              : 0.15
% 4.09/1.72  CNF conversion       : 0.02
% 4.09/1.72  Main loop            : 0.67
% 4.09/1.72  Inferencing          : 0.23
% 4.09/1.72  Reduction            : 0.14
% 4.09/1.72  Demodulation         : 0.12
% 4.09/1.72  BG Simplification    : 0.03
% 4.09/1.72  Subsumption          : 0.22
% 4.09/1.72  Abstraction          : 0.04
% 4.09/1.72  MUC search           : 0.00
% 4.09/1.72  Cooper               : 0.00
% 4.09/1.72  Total                : 0.99
% 4.09/1.72  Index Insertion      : 0.00
% 4.09/1.72  Index Deletion       : 0.00
% 4.09/1.72  Index Matching       : 0.00
% 4.09/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
