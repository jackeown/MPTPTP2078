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
% DateTime   : Thu Dec  3 09:57:08 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   53 (  81 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 174 expanded)
%              Number of equality atoms :   10 (  23 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(D,C)
          & r1_tarski(C,k2_zfmisc_1(A,B))
          & ! [E] :
              ( m1_subset_1(E,A)
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => D != k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_74,axiom,(
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
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( v1_xboole_0(k2_zfmisc_1(A_9,B_10))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_31,plain,(
    ! [B_25,A_26] :
      ( ~ v1_xboole_0(B_25)
      | ~ r2_hidden(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_35,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_31])).

tff(c_28,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(A_39,B_40) = B_40
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    k2_xboole_0('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(k2_xboole_0(A_1,B_2))
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2])).

tff(c_77,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_74])).

tff(c_95,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_77])).

tff(c_79,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( r2_hidden('#skF_1'(A_45,B_46,C_47,D_48),B_46)
      | ~ r2_hidden(D_48,A_45)
      | ~ r1_tarski(A_45,k2_zfmisc_1(B_46,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( m1_subset_1(B_18,A_17)
      | ~ r2_hidden(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_206,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( m1_subset_1('#skF_1'(A_111,B_112,C_113,D_114),B_112)
      | v1_xboole_0(B_112)
      | ~ r2_hidden(D_114,A_111)
      | ~ r1_tarski(A_111,k2_zfmisc_1(B_112,C_113)) ) ),
    inference(resolution,[status(thm)],[c_79,c_18])).

tff(c_208,plain,(
    ! [D_114] :
      ( m1_subset_1('#skF_1'('#skF_5','#skF_3','#skF_4',D_114),'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ r2_hidden(D_114,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_206])).

tff(c_212,plain,(
    ! [D_115] :
      ( m1_subset_1('#skF_1'('#skF_5','#skF_3','#skF_4',D_115),'#skF_3')
      | ~ r2_hidden(D_115,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_208])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k2_zfmisc_1(A_7,B_8))
      | ~ v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_96,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( r2_hidden('#skF_2'(A_49,B_50,C_51,D_52),C_51)
      | ~ r2_hidden(D_52,A_49)
      | ~ r1_tarski(A_49,k2_zfmisc_1(B_50,C_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_184,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( m1_subset_1('#skF_2'(A_105,B_106,C_107,D_108),C_107)
      | v1_xboole_0(C_107)
      | ~ r2_hidden(D_108,A_105)
      | ~ r1_tarski(A_105,k2_zfmisc_1(B_106,C_107)) ) ),
    inference(resolution,[status(thm)],[c_96,c_18])).

tff(c_186,plain,(
    ! [D_108] :
      ( m1_subset_1('#skF_2'('#skF_5','#skF_3','#skF_4',D_108),'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r2_hidden(D_108,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_184])).

tff(c_190,plain,(
    ! [D_109] :
      ( m1_subset_1('#skF_2'('#skF_5','#skF_3','#skF_4',D_109),'#skF_4')
      | ~ r2_hidden(D_109,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_186])).

tff(c_146,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( k4_tarski('#skF_1'(A_69,B_70,C_71,D_72),'#skF_2'(A_69,B_70,C_71,D_72)) = D_72
      | ~ r2_hidden(D_72,A_69)
      | ~ r1_tarski(A_69,k2_zfmisc_1(B_70,C_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [E_22,F_24] :
      ( k4_tarski(E_22,F_24) != '#skF_6'
      | ~ m1_subset_1(F_24,'#skF_4')
      | ~ m1_subset_1(E_22,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_151,plain,(
    ! [D_72,A_69,B_70,C_71] :
      ( D_72 != '#skF_6'
      | ~ m1_subset_1('#skF_2'(A_69,B_70,C_71,D_72),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_69,B_70,C_71,D_72),'#skF_3')
      | ~ r2_hidden(D_72,A_69)
      | ~ r1_tarski(A_69,k2_zfmisc_1(B_70,C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_26])).

tff(c_192,plain,(
    ! [D_109] :
      ( D_109 != '#skF_6'
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_3','#skF_4',D_109),'#skF_3')
      | ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(D_109,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_190,c_151])).

tff(c_198,plain,(
    ! [D_109] :
      ( D_109 != '#skF_6'
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_3','#skF_4',D_109),'#skF_3')
      | ~ r2_hidden(D_109,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_192])).

tff(c_221,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_212,c_198])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:01:47 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.32  
% 2.27/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.27/1.33  
% 2.27/1.33  %Foreground sorts:
% 2.27/1.33  
% 2.27/1.33  
% 2.27/1.33  %Background operators:
% 2.27/1.33  
% 2.27/1.33  
% 2.27/1.33  %Foreground operators:
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.27/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.27/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.27/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.27/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.33  
% 2.27/1.34  tff(f_48, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 2.27/1.34  tff(f_89, negated_conjecture, ~(![A, B, C, D]: ~((r2_hidden(D, C) & r1_tarski(C, k2_zfmisc_1(A, B))) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => ~(D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_subset_1)).
% 2.27/1.34  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 2.27/1.34  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.27/1.34  tff(f_31, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_xboole_0)).
% 2.27/1.34  tff(f_61, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 2.27/1.34  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.27/1.34  tff(f_44, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.27/1.34  tff(c_10, plain, (![A_9, B_10]: (v1_xboole_0(k2_zfmisc_1(A_9, B_10)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.27/1.34  tff(c_30, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.27/1.34  tff(c_31, plain, (![B_25, A_26]: (~v1_xboole_0(B_25) | ~r2_hidden(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.27/1.34  tff(c_35, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_31])).
% 2.27/1.34  tff(c_28, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.27/1.34  tff(c_46, plain, (![A_39, B_40]: (k2_xboole_0(A_39, B_40)=B_40 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.34  tff(c_50, plain, (k2_xboole_0('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_46])).
% 2.27/1.34  tff(c_2, plain, (![A_1, B_2]: (~v1_xboole_0(k2_xboole_0(A_1, B_2)) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.34  tff(c_74, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_50, c_2])).
% 2.27/1.34  tff(c_77, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_35, c_74])).
% 2.27/1.34  tff(c_95, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_10, c_77])).
% 2.27/1.34  tff(c_79, plain, (![A_45, B_46, C_47, D_48]: (r2_hidden('#skF_1'(A_45, B_46, C_47, D_48), B_46) | ~r2_hidden(D_48, A_45) | ~r1_tarski(A_45, k2_zfmisc_1(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.27/1.34  tff(c_18, plain, (![B_18, A_17]: (m1_subset_1(B_18, A_17) | ~r2_hidden(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.27/1.34  tff(c_206, plain, (![A_111, B_112, C_113, D_114]: (m1_subset_1('#skF_1'(A_111, B_112, C_113, D_114), B_112) | v1_xboole_0(B_112) | ~r2_hidden(D_114, A_111) | ~r1_tarski(A_111, k2_zfmisc_1(B_112, C_113)))), inference(resolution, [status(thm)], [c_79, c_18])).
% 2.27/1.34  tff(c_208, plain, (![D_114]: (m1_subset_1('#skF_1'('#skF_5', '#skF_3', '#skF_4', D_114), '#skF_3') | v1_xboole_0('#skF_3') | ~r2_hidden(D_114, '#skF_5'))), inference(resolution, [status(thm)], [c_28, c_206])).
% 2.27/1.34  tff(c_212, plain, (![D_115]: (m1_subset_1('#skF_1'('#skF_5', '#skF_3', '#skF_4', D_115), '#skF_3') | ~r2_hidden(D_115, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_95, c_208])).
% 2.27/1.34  tff(c_8, plain, (![A_7, B_8]: (v1_xboole_0(k2_zfmisc_1(A_7, B_8)) | ~v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.27/1.34  tff(c_94, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_8, c_77])).
% 2.27/1.34  tff(c_96, plain, (![A_49, B_50, C_51, D_52]: (r2_hidden('#skF_2'(A_49, B_50, C_51, D_52), C_51) | ~r2_hidden(D_52, A_49) | ~r1_tarski(A_49, k2_zfmisc_1(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.27/1.34  tff(c_184, plain, (![A_105, B_106, C_107, D_108]: (m1_subset_1('#skF_2'(A_105, B_106, C_107, D_108), C_107) | v1_xboole_0(C_107) | ~r2_hidden(D_108, A_105) | ~r1_tarski(A_105, k2_zfmisc_1(B_106, C_107)))), inference(resolution, [status(thm)], [c_96, c_18])).
% 2.27/1.34  tff(c_186, plain, (![D_108]: (m1_subset_1('#skF_2'('#skF_5', '#skF_3', '#skF_4', D_108), '#skF_4') | v1_xboole_0('#skF_4') | ~r2_hidden(D_108, '#skF_5'))), inference(resolution, [status(thm)], [c_28, c_184])).
% 2.27/1.34  tff(c_190, plain, (![D_109]: (m1_subset_1('#skF_2'('#skF_5', '#skF_3', '#skF_4', D_109), '#skF_4') | ~r2_hidden(D_109, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_94, c_186])).
% 2.27/1.34  tff(c_146, plain, (![A_69, B_70, C_71, D_72]: (k4_tarski('#skF_1'(A_69, B_70, C_71, D_72), '#skF_2'(A_69, B_70, C_71, D_72))=D_72 | ~r2_hidden(D_72, A_69) | ~r1_tarski(A_69, k2_zfmisc_1(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.27/1.34  tff(c_26, plain, (![E_22, F_24]: (k4_tarski(E_22, F_24)!='#skF_6' | ~m1_subset_1(F_24, '#skF_4') | ~m1_subset_1(E_22, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.27/1.34  tff(c_151, plain, (![D_72, A_69, B_70, C_71]: (D_72!='#skF_6' | ~m1_subset_1('#skF_2'(A_69, B_70, C_71, D_72), '#skF_4') | ~m1_subset_1('#skF_1'(A_69, B_70, C_71, D_72), '#skF_3') | ~r2_hidden(D_72, A_69) | ~r1_tarski(A_69, k2_zfmisc_1(B_70, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_26])).
% 2.27/1.34  tff(c_192, plain, (![D_109]: (D_109!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_5', '#skF_3', '#skF_4', D_109), '#skF_3') | ~r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(D_109, '#skF_5'))), inference(resolution, [status(thm)], [c_190, c_151])).
% 2.27/1.34  tff(c_198, plain, (![D_109]: (D_109!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_5', '#skF_3', '#skF_4', D_109), '#skF_3') | ~r2_hidden(D_109, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_192])).
% 2.27/1.34  tff(c_221, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_212, c_198])).
% 2.27/1.34  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_30])).
% 2.27/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.34  
% 2.27/1.34  Inference rules
% 2.27/1.34  ----------------------
% 2.27/1.34  #Ref     : 0
% 2.27/1.34  #Sup     : 43
% 2.27/1.34  #Fact    : 0
% 2.27/1.34  #Define  : 0
% 2.27/1.34  #Split   : 0
% 2.27/1.34  #Chain   : 0
% 2.27/1.34  #Close   : 0
% 2.27/1.34  
% 2.27/1.34  Ordering : KBO
% 2.27/1.34  
% 2.27/1.34  Simplification rules
% 2.27/1.34  ----------------------
% 2.27/1.34  #Subsume      : 14
% 2.27/1.34  #Demod        : 1
% 2.27/1.34  #Tautology    : 7
% 2.27/1.34  #SimpNegUnit  : 7
% 2.27/1.34  #BackRed      : 1
% 2.27/1.34  
% 2.27/1.34  #Partial instantiations: 0
% 2.27/1.34  #Strategies tried      : 1
% 2.27/1.34  
% 2.27/1.34  Timing (in seconds)
% 2.27/1.34  ----------------------
% 2.27/1.34  Preprocessing        : 0.30
% 2.27/1.34  Parsing              : 0.17
% 2.27/1.34  CNF conversion       : 0.02
% 2.27/1.34  Main loop            : 0.22
% 2.27/1.34  Inferencing          : 0.10
% 2.27/1.34  Reduction            : 0.05
% 2.27/1.34  Demodulation         : 0.03
% 2.27/1.34  BG Simplification    : 0.02
% 2.27/1.35  Subsumption          : 0.05
% 2.27/1.35  Abstraction          : 0.01
% 2.27/1.35  MUC search           : 0.00
% 2.27/1.35  Cooper               : 0.00
% 2.27/1.35  Total                : 0.55
% 2.27/1.35  Index Insertion      : 0.00
% 2.27/1.35  Index Deletion       : 0.00
% 2.27/1.35  Index Matching       : 0.00
% 2.27/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
