%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:09 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   63 (  99 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 161 expanded)
%              Number of equality atoms :   18 (  48 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_32,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_78,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_87,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_78])).

tff(c_38,plain,
    ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_57,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_88,plain,(
    k1_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,(
    ! [D_39] :
      ( r2_hidden(k4_tarski(D_39,'#skF_9'(D_39)),'#skF_8')
      | ~ r2_hidden(D_39,'#skF_7')
      | k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_99,plain,(
    ! [D_39] :
      ( r2_hidden(k4_tarski(D_39,'#skF_9'(D_39)),'#skF_8')
      | ~ r2_hidden(D_39,'#skF_7')
      | k1_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_44])).

tff(c_101,plain,(
    ! [D_65] :
      ( r2_hidden(k4_tarski(D_65,'#skF_9'(D_65)),'#skF_8')
      | ~ r2_hidden(D_65,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_99])).

tff(c_18,plain,(
    ! [C_23,A_8,D_26] :
      ( r2_hidden(C_23,k1_relat_1(A_8))
      | ~ r2_hidden(k4_tarski(C_23,D_26),A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_106,plain,(
    ! [D_66] :
      ( r2_hidden(D_66,k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_66,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_101,c_18])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),A_3)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_118,plain,(
    ! [B_69] :
      ( ~ r2_xboole_0(k1_relat_1('#skF_8'),B_69)
      | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_8'),B_69),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_106,c_8])).

tff(c_123,plain,(
    ~ r2_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_118])).

tff(c_126,plain,
    ( k1_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2,c_123])).

tff(c_129,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_126])).

tff(c_182,plain,(
    ! [A_78,B_79,C_80] :
      ( m1_subset_1(k1_relset_1(A_78,B_79,C_80),k1_zfmisc_1(A_78))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_192,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_182])).

tff(c_196,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_192])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_199,plain,(
    r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_196,c_12])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_199])).

tff(c_204,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_205,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_232,plain,(
    ! [A_91,B_92,C_93] :
      ( k1_relset_1(A_91,B_92,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_239,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_232])).

tff(c_242,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_239])).

tff(c_254,plain,(
    ! [C_97,A_98] :
      ( r2_hidden(k4_tarski(C_97,'#skF_5'(A_98,k1_relat_1(A_98),C_97)),A_98)
      | ~ r2_hidden(C_97,k1_relat_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [E_42] :
      ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski('#skF_10',E_42),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_230,plain,(
    ! [E_42] : ~ r2_hidden(k4_tarski('#skF_10',E_42),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_34])).

tff(c_258,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_254,c_230])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_242,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.33  
% 2.06/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.33  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.06/1.33  
% 2.06/1.33  %Foreground sorts:
% 2.06/1.33  
% 2.06/1.33  
% 2.06/1.33  %Background operators:
% 2.06/1.33  
% 2.06/1.33  
% 2.06/1.33  %Foreground operators:
% 2.06/1.33  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.06/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.06/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.06/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.06/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.33  tff('#skF_10', type, '#skF_10': $i).
% 2.06/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.06/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.06/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.33  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.06/1.33  tff('#skF_8', type, '#skF_8': $i).
% 2.06/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.06/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.33  
% 2.06/1.35  tff(f_75, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 2.06/1.35  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.06/1.35  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.06/1.35  tff(f_42, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.06/1.35  tff(f_54, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.06/1.35  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.06/1.35  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.06/1.35  tff(c_32, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.06/1.35  tff(c_78, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.35  tff(c_87, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_78])).
% 2.06/1.35  tff(c_38, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.06/1.35  tff(c_57, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_38])).
% 2.06/1.35  tff(c_88, plain, (k1_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_57])).
% 2.06/1.35  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.35  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.35  tff(c_44, plain, (![D_39]: (r2_hidden(k4_tarski(D_39, '#skF_9'(D_39)), '#skF_8') | ~r2_hidden(D_39, '#skF_7') | k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.06/1.35  tff(c_99, plain, (![D_39]: (r2_hidden(k4_tarski(D_39, '#skF_9'(D_39)), '#skF_8') | ~r2_hidden(D_39, '#skF_7') | k1_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_44])).
% 2.06/1.35  tff(c_101, plain, (![D_65]: (r2_hidden(k4_tarski(D_65, '#skF_9'(D_65)), '#skF_8') | ~r2_hidden(D_65, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_88, c_99])).
% 2.06/1.35  tff(c_18, plain, (![C_23, A_8, D_26]: (r2_hidden(C_23, k1_relat_1(A_8)) | ~r2_hidden(k4_tarski(C_23, D_26), A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.06/1.35  tff(c_106, plain, (![D_66]: (r2_hidden(D_66, k1_relat_1('#skF_8')) | ~r2_hidden(D_66, '#skF_7'))), inference(resolution, [status(thm)], [c_101, c_18])).
% 2.06/1.35  tff(c_8, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), A_3) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.35  tff(c_118, plain, (![B_69]: (~r2_xboole_0(k1_relat_1('#skF_8'), B_69) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_8'), B_69), '#skF_7'))), inference(resolution, [status(thm)], [c_106, c_8])).
% 2.06/1.35  tff(c_123, plain, (~r2_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_10, c_118])).
% 2.06/1.35  tff(c_126, plain, (k1_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_2, c_123])).
% 2.06/1.35  tff(c_129, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_88, c_126])).
% 2.06/1.35  tff(c_182, plain, (![A_78, B_79, C_80]: (m1_subset_1(k1_relset_1(A_78, B_79, C_80), k1_zfmisc_1(A_78)) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.06/1.35  tff(c_192, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_87, c_182])).
% 2.06/1.35  tff(c_196, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_192])).
% 2.06/1.35  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.35  tff(c_199, plain, (r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_196, c_12])).
% 2.06/1.35  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_199])).
% 2.06/1.35  tff(c_204, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_38])).
% 2.06/1.35  tff(c_205, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_38])).
% 2.06/1.35  tff(c_232, plain, (![A_91, B_92, C_93]: (k1_relset_1(A_91, B_92, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.35  tff(c_239, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_232])).
% 2.06/1.35  tff(c_242, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_205, c_239])).
% 2.06/1.35  tff(c_254, plain, (![C_97, A_98]: (r2_hidden(k4_tarski(C_97, '#skF_5'(A_98, k1_relat_1(A_98), C_97)), A_98) | ~r2_hidden(C_97, k1_relat_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.06/1.35  tff(c_34, plain, (![E_42]: (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski('#skF_10', E_42), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.06/1.35  tff(c_230, plain, (![E_42]: (~r2_hidden(k4_tarski('#skF_10', E_42), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_34])).
% 2.06/1.35  tff(c_258, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_254, c_230])).
% 2.06/1.35  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_242, c_258])).
% 2.06/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.35  
% 2.06/1.35  Inference rules
% 2.06/1.35  ----------------------
% 2.06/1.35  #Ref     : 0
% 2.06/1.35  #Sup     : 42
% 2.06/1.35  #Fact    : 0
% 2.06/1.35  #Define  : 0
% 2.06/1.35  #Split   : 2
% 2.06/1.35  #Chain   : 0
% 2.06/1.35  #Close   : 0
% 2.06/1.35  
% 2.06/1.35  Ordering : KBO
% 2.06/1.35  
% 2.06/1.35  Simplification rules
% 2.06/1.35  ----------------------
% 2.06/1.35  #Subsume      : 4
% 2.06/1.35  #Demod        : 11
% 2.06/1.35  #Tautology    : 16
% 2.06/1.35  #SimpNegUnit  : 3
% 2.06/1.35  #BackRed      : 1
% 2.06/1.35  
% 2.06/1.35  #Partial instantiations: 0
% 2.06/1.35  #Strategies tried      : 1
% 2.06/1.35  
% 2.06/1.35  Timing (in seconds)
% 2.06/1.35  ----------------------
% 2.06/1.35  Preprocessing        : 0.29
% 2.06/1.35  Parsing              : 0.14
% 2.06/1.35  CNF conversion       : 0.02
% 2.06/1.35  Main loop            : 0.18
% 2.06/1.35  Inferencing          : 0.07
% 2.06/1.35  Reduction            : 0.05
% 2.06/1.35  Demodulation         : 0.03
% 2.06/1.35  BG Simplification    : 0.01
% 2.06/1.35  Subsumption          : 0.03
% 2.06/1.35  Abstraction          : 0.01
% 2.06/1.35  MUC search           : 0.00
% 2.06/1.35  Cooper               : 0.00
% 2.06/1.35  Total                : 0.50
% 2.06/1.35  Index Insertion      : 0.00
% 2.06/1.35  Index Deletion       : 0.00
% 2.06/1.35  Index Matching       : 0.00
% 2.06/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
