%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:55 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 182 expanded)
%              Number of leaves         :   26 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 410 expanded)
%              Number of equality atoms :   45 ( 138 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_34,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_101,plain,(
    ! [A_42,B_43] :
      ( k6_setfam_1(A_42,B_43) = k1_setfam_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_101])).

tff(c_124,plain,(
    ! [A_50,B_51] :
      ( k8_setfam_1(A_50,B_51) = k6_setfam_1(A_50,B_51)
      | k1_xboole_0 = B_51
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_127,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_36,c_124])).

tff(c_129,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_127])).

tff(c_130,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_6,plain,(
    ! [A_5] :
      ( k8_setfam_1(A_5,k1_xboole_0) = A_5
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_185,plain,(
    ! [A_58] :
      ( k8_setfam_1(A_58,'#skF_7') = A_58
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(A_58))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_6])).

tff(c_189,plain,(
    k8_setfam_1('#skF_5','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_185])).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,(
    ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_190,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_55])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_190])).

tff(c_194,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_196,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_55])).

tff(c_195,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_201,plain,(
    ! [A_59,C_60] :
      ( r2_hidden('#skF_1'(A_59,k1_setfam_1(A_59),C_60),A_59)
      | r2_hidden(C_60,k1_setfam_1(A_59))
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ! [D_30] :
      ( r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7'))
      | r2_hidden('#skF_6',D_30)
      | ~ r2_hidden(D_30,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_99,plain,(
    ! [D_30] :
      ( r2_hidden('#skF_6',D_30)
      | ~ r2_hidden(D_30,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_48])).

tff(c_210,plain,(
    ! [C_60] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_60))
      | r2_hidden(C_60,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_201,c_99])).

tff(c_226,plain,(
    ! [C_61] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_61))
      | r2_hidden(C_61,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_210])).

tff(c_24,plain,(
    ! [C_19,A_7] :
      ( ~ r2_hidden(C_19,'#skF_1'(A_7,k1_setfam_1(A_7),C_19))
      | r2_hidden(C_19,k1_setfam_1(A_7))
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_230,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_226,c_24])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_195,c_196,c_230])).

tff(c_240,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_241,plain,(
    r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_243,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_40])).

tff(c_244,plain,(
    ! [A_62,B_63] :
      ( k2_xboole_0(k1_tarski(A_62),B_63) = B_63
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),B_4) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_256,plain,(
    ! [B_64,A_65] :
      ( k1_xboole_0 != B_64
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_4])).

tff(c_266,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(resolution,[status(thm)],[c_243,c_256])).

tff(c_271,plain,(
    ! [A_67,B_68] :
      ( k6_setfam_1(A_67,B_68) = k1_setfam_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_275,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_271])).

tff(c_300,plain,(
    ! [A_75,B_76] :
      ( k8_setfam_1(A_75,B_76) = k6_setfam_1(A_75,B_76)
      | k1_xboole_0 = B_76
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(A_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_303,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_36,c_300])).

tff(c_305,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_303])).

tff(c_306,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_305])).

tff(c_309,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_241])).

tff(c_281,plain,(
    ! [C_69,D_70,A_71] :
      ( r2_hidden(C_69,D_70)
      | ~ r2_hidden(D_70,A_71)
      | ~ r2_hidden(C_69,k1_setfam_1(A_71))
      | k1_xboole_0 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_283,plain,(
    ! [C_69] :
      ( r2_hidden(C_69,'#skF_8')
      | ~ r2_hidden(C_69,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_243,c_281])).

tff(c_290,plain,(
    ! [C_69] :
      ( r2_hidden(C_69,'#skF_8')
      | ~ r2_hidden(C_69,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_283])).

tff(c_323,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_309,c_290])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:41:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.30  
% 2.01/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.31  %$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 2.01/1.31  
% 2.01/1.31  %Foreground sorts:
% 2.01/1.31  
% 2.01/1.31  
% 2.01/1.31  %Background operators:
% 2.01/1.31  
% 2.01/1.31  
% 2.01/1.31  %Foreground operators:
% 2.01/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.01/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.31  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.01/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.01/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.01/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.01/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.01/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.31  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.01/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.01/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.01/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.01/1.31  
% 2.28/1.32  tff(f_78, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_setfam_1)).
% 2.28/1.32  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.28/1.32  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.28/1.32  tff(f_62, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.28/1.32  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.28/1.32  tff(f_32, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.28/1.32  tff(c_34, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.28/1.32  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.28/1.32  tff(c_101, plain, (![A_42, B_43]: (k6_setfam_1(A_42, B_43)=k1_setfam_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.32  tff(c_105, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_36, c_101])).
% 2.28/1.32  tff(c_124, plain, (![A_50, B_51]: (k8_setfam_1(A_50, B_51)=k6_setfam_1(A_50, B_51) | k1_xboole_0=B_51 | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_50))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.32  tff(c_127, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_36, c_124])).
% 2.28/1.32  tff(c_129, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_127])).
% 2.28/1.32  tff(c_130, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_129])).
% 2.28/1.32  tff(c_6, plain, (![A_5]: (k8_setfam_1(A_5, k1_xboole_0)=A_5 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.32  tff(c_185, plain, (![A_58]: (k8_setfam_1(A_58, '#skF_7')=A_58 | ~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(A_58))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_6])).
% 2.28/1.32  tff(c_189, plain, (k8_setfam_1('#skF_5', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_36, c_185])).
% 2.28/1.32  tff(c_38, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.28/1.32  tff(c_55, plain, (~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.28/1.32  tff(c_190, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_55])).
% 2.28/1.32  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_190])).
% 2.28/1.32  tff(c_194, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(splitRight, [status(thm)], [c_129])).
% 2.28/1.32  tff(c_196, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_55])).
% 2.28/1.32  tff(c_195, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_129])).
% 2.28/1.32  tff(c_201, plain, (![A_59, C_60]: (r2_hidden('#skF_1'(A_59, k1_setfam_1(A_59), C_60), A_59) | r2_hidden(C_60, k1_setfam_1(A_59)) | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.32  tff(c_48, plain, (![D_30]: (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7')) | r2_hidden('#skF_6', D_30) | ~r2_hidden(D_30, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.28/1.32  tff(c_99, plain, (![D_30]: (r2_hidden('#skF_6', D_30) | ~r2_hidden(D_30, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_55, c_48])).
% 2.28/1.32  tff(c_210, plain, (![C_60]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_60)) | r2_hidden(C_60, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_201, c_99])).
% 2.28/1.32  tff(c_226, plain, (![C_61]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_61)) | r2_hidden(C_61, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_195, c_210])).
% 2.28/1.32  tff(c_24, plain, (![C_19, A_7]: (~r2_hidden(C_19, '#skF_1'(A_7, k1_setfam_1(A_7), C_19)) | r2_hidden(C_19, k1_setfam_1(A_7)) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.32  tff(c_230, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_226, c_24])).
% 2.28/1.32  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_195, c_196, c_230])).
% 2.28/1.32  tff(c_240, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_38])).
% 2.28/1.32  tff(c_241, plain, (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_38])).
% 2.28/1.32  tff(c_40, plain, (r2_hidden('#skF_8', '#skF_7') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.28/1.32  tff(c_243, plain, (r2_hidden('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_40])).
% 2.28/1.32  tff(c_244, plain, (![A_62, B_63]: (k2_xboole_0(k1_tarski(A_62), B_63)=B_63 | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.32  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.32  tff(c_256, plain, (![B_64, A_65]: (k1_xboole_0!=B_64 | ~r2_hidden(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_244, c_4])).
% 2.28/1.32  tff(c_266, plain, (k1_xboole_0!='#skF_7'), inference(resolution, [status(thm)], [c_243, c_256])).
% 2.28/1.32  tff(c_271, plain, (![A_67, B_68]: (k6_setfam_1(A_67, B_68)=k1_setfam_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.32  tff(c_275, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_36, c_271])).
% 2.28/1.32  tff(c_300, plain, (![A_75, B_76]: (k8_setfam_1(A_75, B_76)=k6_setfam_1(A_75, B_76) | k1_xboole_0=B_76 | ~m1_subset_1(B_76, k1_zfmisc_1(k1_zfmisc_1(A_75))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.32  tff(c_303, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_36, c_300])).
% 2.28/1.32  tff(c_305, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_303])).
% 2.28/1.32  tff(c_306, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_266, c_305])).
% 2.28/1.32  tff(c_309, plain, (r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_241])).
% 2.28/1.32  tff(c_281, plain, (![C_69, D_70, A_71]: (r2_hidden(C_69, D_70) | ~r2_hidden(D_70, A_71) | ~r2_hidden(C_69, k1_setfam_1(A_71)) | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.32  tff(c_283, plain, (![C_69]: (r2_hidden(C_69, '#skF_8') | ~r2_hidden(C_69, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_243, c_281])).
% 2.28/1.32  tff(c_290, plain, (![C_69]: (r2_hidden(C_69, '#skF_8') | ~r2_hidden(C_69, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_266, c_283])).
% 2.28/1.32  tff(c_323, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_309, c_290])).
% 2.28/1.32  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_323])).
% 2.28/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.32  
% 2.28/1.32  Inference rules
% 2.28/1.32  ----------------------
% 2.28/1.32  #Ref     : 0
% 2.28/1.32  #Sup     : 59
% 2.28/1.32  #Fact    : 0
% 2.28/1.32  #Define  : 0
% 2.28/1.32  #Split   : 4
% 2.28/1.32  #Chain   : 0
% 2.28/1.32  #Close   : 0
% 2.28/1.32  
% 2.28/1.32  Ordering : KBO
% 2.28/1.32  
% 2.28/1.32  Simplification rules
% 2.28/1.32  ----------------------
% 2.28/1.32  #Subsume      : 5
% 2.28/1.32  #Demod        : 30
% 2.28/1.32  #Tautology    : 33
% 2.28/1.32  #SimpNegUnit  : 16
% 2.28/1.32  #BackRed      : 14
% 2.28/1.32  
% 2.28/1.32  #Partial instantiations: 0
% 2.28/1.32  #Strategies tried      : 1
% 2.28/1.32  
% 2.28/1.32  Timing (in seconds)
% 2.28/1.32  ----------------------
% 2.28/1.33  Preprocessing        : 0.33
% 2.28/1.33  Parsing              : 0.17
% 2.28/1.33  CNF conversion       : 0.03
% 2.28/1.33  Main loop            : 0.20
% 2.28/1.33  Inferencing          : 0.07
% 2.28/1.33  Reduction            : 0.07
% 2.28/1.33  Demodulation         : 0.04
% 2.28/1.33  BG Simplification    : 0.02
% 2.28/1.33  Subsumption          : 0.03
% 2.28/1.33  Abstraction          : 0.01
% 2.28/1.33  MUC search           : 0.00
% 2.28/1.33  Cooper               : 0.00
% 2.28/1.33  Total                : 0.57
% 2.28/1.33  Index Insertion      : 0.00
% 2.28/1.33  Index Deletion       : 0.00
% 2.28/1.33  Index Matching       : 0.00
% 2.28/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
