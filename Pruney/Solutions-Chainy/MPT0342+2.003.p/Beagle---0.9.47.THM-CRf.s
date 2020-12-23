%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:16 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 110 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 249 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                   => r2_hidden(D,C) ) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_44,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_143,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_2'(A_45,B_46),A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    ! [A_48,B_49] :
      ( ~ v1_xboole_0(A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_143,c_2])).

tff(c_167,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_163,c_26])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( m1_subset_1(B_14,A_13)
      | ~ r2_hidden(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_158,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1('#skF_2'(A_45,B_46),A_45)
      | v1_xboole_0(A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_143,c_16])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_15] : ~ v1_xboole_0(k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_96,plain,(
    ! [B_40,A_41] :
      ( r2_hidden(B_40,A_41)
      | ~ m1_subset_1(B_40,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_12] : k3_tarski(k1_zfmisc_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,k3_tarski(B_32))
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [A_31,A_12] :
      ( r1_tarski(A_31,A_12)
      | ~ r2_hidden(A_31,k1_zfmisc_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_68])).

tff(c_107,plain,(
    ! [B_40,A_12] :
      ( r1_tarski(B_40,A_12)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_96,c_71])).

tff(c_122,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(B_43,A_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_107])).

tff(c_141,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_122])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_169,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_182,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53),B_54)
      | ~ r1_tarski(A_53,B_54)
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_4,c_169])).

tff(c_199,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | ~ r1_tarski(A_56,B_55)
      | v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_182,c_2])).

tff(c_211,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_199])).

tff(c_225,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_211])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(B_14,A_13)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_982,plain,(
    ! [B_131,B_132,A_133] :
      ( r2_hidden(B_131,B_132)
      | ~ r1_tarski(A_133,B_132)
      | ~ m1_subset_1(B_131,A_133)
      | v1_xboole_0(A_133) ) ),
    inference(resolution,[status(thm)],[c_18,c_169])).

tff(c_996,plain,(
    ! [B_131] :
      ( r2_hidden(B_131,'#skF_3')
      | ~ m1_subset_1(B_131,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_141,c_982])).

tff(c_1030,plain,(
    ! [B_135] :
      ( r2_hidden(B_135,'#skF_3')
      | ~ m1_subset_1(B_135,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_996])).

tff(c_1035,plain,(
    ! [B_135] :
      ( m1_subset_1(B_135,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_135,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1030,c_16])).

tff(c_1080,plain,(
    ! [B_138] :
      ( m1_subset_1(B_138,'#skF_3')
      | ~ m1_subset_1(B_138,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_1035])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [D_20] :
      ( r2_hidden(D_20,'#skF_5')
      | ~ r2_hidden(D_20,'#skF_4')
      | ~ m1_subset_1(D_20,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden('#skF_2'(A_36,B_37),B_37)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_783,plain,(
    ! [A_116] :
      ( r1_tarski(A_116,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_116,'#skF_5'),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_116,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_787,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_783])).

tff(c_793,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_787])).

tff(c_1098,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1080,c_793])).

tff(c_1102,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_158,c_1098])).

tff(c_1109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_167,c_1102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:16:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.77/1.41  
% 2.77/1.41  %Foreground sorts:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Background operators:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Foreground operators:
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.77/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.77/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.41  
% 2.77/1.43  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.77/1.43  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.77/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.77/1.43  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.77/1.43  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.77/1.43  tff(f_44, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.77/1.43  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.77/1.43  tff(c_26, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.77/1.43  tff(c_143, plain, (![A_45, B_46]: (r2_hidden('#skF_2'(A_45, B_46), A_45) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.77/1.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.43  tff(c_163, plain, (![A_48, B_49]: (~v1_xboole_0(A_48) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_143, c_2])).
% 2.77/1.43  tff(c_167, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_163, c_26])).
% 2.77/1.43  tff(c_16, plain, (![B_14, A_13]: (m1_subset_1(B_14, A_13) | ~r2_hidden(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.43  tff(c_158, plain, (![A_45, B_46]: (m1_subset_1('#skF_2'(A_45, B_46), A_45) | v1_xboole_0(A_45) | r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_143, c_16])).
% 2.77/1.43  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.77/1.43  tff(c_24, plain, (![A_15]: (~v1_xboole_0(k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.77/1.43  tff(c_96, plain, (![B_40, A_41]: (r2_hidden(B_40, A_41) | ~m1_subset_1(B_40, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.43  tff(c_14, plain, (![A_12]: (k3_tarski(k1_zfmisc_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.77/1.43  tff(c_68, plain, (![A_31, B_32]: (r1_tarski(A_31, k3_tarski(B_32)) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.77/1.43  tff(c_71, plain, (![A_31, A_12]: (r1_tarski(A_31, A_12) | ~r2_hidden(A_31, k1_zfmisc_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_68])).
% 2.77/1.43  tff(c_107, plain, (![B_40, A_12]: (r1_tarski(B_40, A_12) | ~m1_subset_1(B_40, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_96, c_71])).
% 2.77/1.43  tff(c_122, plain, (![B_43, A_44]: (r1_tarski(B_43, A_44) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)))), inference(negUnitSimplification, [status(thm)], [c_24, c_107])).
% 2.77/1.43  tff(c_141, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_122])).
% 2.77/1.43  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.43  tff(c_169, plain, (![C_50, B_51, A_52]: (r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.77/1.43  tff(c_182, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53), B_54) | ~r1_tarski(A_53, B_54) | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_4, c_169])).
% 2.77/1.43  tff(c_199, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | ~r1_tarski(A_56, B_55) | v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_182, c_2])).
% 2.77/1.43  tff(c_211, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_141, c_199])).
% 2.77/1.43  tff(c_225, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_167, c_211])).
% 2.77/1.43  tff(c_18, plain, (![B_14, A_13]: (r2_hidden(B_14, A_13) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.43  tff(c_982, plain, (![B_131, B_132, A_133]: (r2_hidden(B_131, B_132) | ~r1_tarski(A_133, B_132) | ~m1_subset_1(B_131, A_133) | v1_xboole_0(A_133))), inference(resolution, [status(thm)], [c_18, c_169])).
% 2.77/1.43  tff(c_996, plain, (![B_131]: (r2_hidden(B_131, '#skF_3') | ~m1_subset_1(B_131, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_141, c_982])).
% 2.77/1.43  tff(c_1030, plain, (![B_135]: (r2_hidden(B_135, '#skF_3') | ~m1_subset_1(B_135, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_167, c_996])).
% 2.77/1.43  tff(c_1035, plain, (![B_135]: (m1_subset_1(B_135, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_135, '#skF_4'))), inference(resolution, [status(thm)], [c_1030, c_16])).
% 2.77/1.43  tff(c_1080, plain, (![B_138]: (m1_subset_1(B_138, '#skF_3') | ~m1_subset_1(B_138, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_225, c_1035])).
% 2.77/1.43  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.77/1.43  tff(c_28, plain, (![D_20]: (r2_hidden(D_20, '#skF_5') | ~r2_hidden(D_20, '#skF_4') | ~m1_subset_1(D_20, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.77/1.43  tff(c_81, plain, (![A_36, B_37]: (~r2_hidden('#skF_2'(A_36, B_37), B_37) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.77/1.43  tff(c_783, plain, (![A_116]: (r1_tarski(A_116, '#skF_5') | ~r2_hidden('#skF_2'(A_116, '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_2'(A_116, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_81])).
% 2.77/1.43  tff(c_787, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_10, c_783])).
% 2.77/1.43  tff(c_793, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_787])).
% 2.77/1.43  tff(c_1098, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1080, c_793])).
% 2.77/1.43  tff(c_1102, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_158, c_1098])).
% 2.77/1.43  tff(c_1109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_167, c_1102])).
% 2.77/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  Inference rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Ref     : 0
% 2.77/1.43  #Sup     : 222
% 2.77/1.43  #Fact    : 0
% 2.77/1.43  #Define  : 0
% 2.77/1.43  #Split   : 3
% 2.77/1.43  #Chain   : 0
% 2.77/1.43  #Close   : 0
% 2.77/1.43  
% 2.77/1.43  Ordering : KBO
% 2.77/1.43  
% 2.77/1.43  Simplification rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Subsume      : 66
% 2.77/1.43  #Demod        : 14
% 2.77/1.43  #Tautology    : 21
% 2.77/1.43  #SimpNegUnit  : 53
% 2.77/1.43  #BackRed      : 0
% 2.77/1.43  
% 2.77/1.43  #Partial instantiations: 0
% 2.77/1.43  #Strategies tried      : 1
% 2.77/1.43  
% 2.77/1.43  Timing (in seconds)
% 2.77/1.43  ----------------------
% 2.77/1.43  Preprocessing        : 0.26
% 2.77/1.43  Parsing              : 0.15
% 2.77/1.43  CNF conversion       : 0.02
% 2.77/1.43  Main loop            : 0.40
% 2.77/1.43  Inferencing          : 0.16
% 2.77/1.43  Reduction            : 0.10
% 2.77/1.43  Demodulation         : 0.06
% 2.77/1.43  BG Simplification    : 0.02
% 2.77/1.43  Subsumption          : 0.09
% 2.77/1.43  Abstraction          : 0.02
% 2.77/1.43  MUC search           : 0.00
% 2.77/1.43  Cooper               : 0.00
% 2.77/1.43  Total                : 0.69
% 2.77/1.43  Index Insertion      : 0.00
% 2.77/1.43  Index Deletion       : 0.00
% 2.77/1.43  Index Matching       : 0.00
% 2.77/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
