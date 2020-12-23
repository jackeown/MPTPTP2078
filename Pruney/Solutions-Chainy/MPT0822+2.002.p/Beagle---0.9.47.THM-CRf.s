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
% DateTime   : Thu Dec  3 10:07:10 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 101 expanded)
%              Number of leaves         :   33 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 163 expanded)
%              Number of equality atoms :   18 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_70,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_70])).

tff(c_76,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_80,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_76])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_92,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_96,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_92])).

tff(c_42,plain,
    ( k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_69,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_98,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_69])).

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

tff(c_48,plain,(
    ! [D_42] :
      ( r2_hidden(k4_tarski('#skF_9'(D_42),D_42),'#skF_8')
      | ~ r2_hidden(D_42,'#skF_7')
      | k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_131,plain,(
    ! [D_42] :
      ( r2_hidden(k4_tarski('#skF_9'(D_42),D_42),'#skF_8')
      | ~ r2_hidden(D_42,'#skF_7')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_48])).

tff(c_133,plain,(
    ! [D_80] :
      ( r2_hidden(k4_tarski('#skF_9'(D_80),D_80),'#skF_8')
      | ~ r2_hidden(D_80,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_131])).

tff(c_18,plain,(
    ! [C_23,A_8,D_26] :
      ( r2_hidden(C_23,k2_relat_1(A_8))
      | ~ r2_hidden(k4_tarski(D_26,C_23),A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_138,plain,(
    ! [D_81] :
      ( r2_hidden(D_81,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_81,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_133,c_18])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),A_3)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_154,plain,(
    ! [B_82] :
      ( ~ r2_xboole_0(k2_relat_1('#skF_8'),B_82)
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_82),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_138,c_8])).

tff(c_159,plain,(
    ~ r2_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_162,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2,c_159])).

tff(c_165,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_162])).

tff(c_168,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_14,c_165])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_80,c_168])).

tff(c_173,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_174,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_205,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_relset_1(A_100,B_101,C_102) = k2_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_208,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_205])).

tff(c_210,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_208])).

tff(c_235,plain,(
    ! [A_105,C_106] :
      ( r2_hidden(k4_tarski('#skF_5'(A_105,k2_relat_1(A_105),C_106),C_106),A_105)
      | ~ r2_hidden(C_106,k2_relat_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    ! [E_45] :
      ( k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski(E_45,'#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_185,plain,(
    ! [E_45] : ~ r2_hidden(k4_tarski(E_45,'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_38])).

tff(c_242,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_235,c_185])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_210,c_242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.27  
% 2.12/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.27  %$ v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.12/1.27  
% 2.12/1.27  %Foreground sorts:
% 2.12/1.27  
% 2.12/1.27  
% 2.12/1.27  %Background operators:
% 2.12/1.27  
% 2.12/1.27  
% 2.12/1.27  %Foreground operators:
% 2.12/1.27  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.12/1.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.12/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.12/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.12/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.27  tff('#skF_10', type, '#skF_10': $i).
% 2.12/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.12/1.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.12/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.12/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.27  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.12/1.27  tff('#skF_8', type, '#skF_8': $i).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.12/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.27  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.12/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.27  
% 2.12/1.28  tff(f_83, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 2.12/1.28  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.12/1.28  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.12/1.28  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.12/1.28  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.12/1.28  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.12/1.28  tff(f_42, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.12/1.28  tff(f_56, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.12/1.28  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.12/1.28  tff(c_70, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.12/1.28  tff(c_74, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_70])).
% 2.12/1.28  tff(c_76, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.28  tff(c_80, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_36, c_76])).
% 2.12/1.28  tff(c_14, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.28  tff(c_92, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.28  tff(c_96, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_92])).
% 2.12/1.28  tff(c_42, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.12/1.28  tff(c_69, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_42])).
% 2.12/1.28  tff(c_98, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_69])).
% 2.12/1.28  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.28  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.12/1.28  tff(c_48, plain, (![D_42]: (r2_hidden(k4_tarski('#skF_9'(D_42), D_42), '#skF_8') | ~r2_hidden(D_42, '#skF_7') | k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.12/1.28  tff(c_131, plain, (![D_42]: (r2_hidden(k4_tarski('#skF_9'(D_42), D_42), '#skF_8') | ~r2_hidden(D_42, '#skF_7') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_48])).
% 2.12/1.28  tff(c_133, plain, (![D_80]: (r2_hidden(k4_tarski('#skF_9'(D_80), D_80), '#skF_8') | ~r2_hidden(D_80, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_98, c_131])).
% 2.12/1.28  tff(c_18, plain, (![C_23, A_8, D_26]: (r2_hidden(C_23, k2_relat_1(A_8)) | ~r2_hidden(k4_tarski(D_26, C_23), A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.28  tff(c_138, plain, (![D_81]: (r2_hidden(D_81, k2_relat_1('#skF_8')) | ~r2_hidden(D_81, '#skF_7'))), inference(resolution, [status(thm)], [c_133, c_18])).
% 2.12/1.28  tff(c_8, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), A_3) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.12/1.28  tff(c_154, plain, (![B_82]: (~r2_xboole_0(k2_relat_1('#skF_8'), B_82) | ~r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_82), '#skF_7'))), inference(resolution, [status(thm)], [c_138, c_8])).
% 2.12/1.28  tff(c_159, plain, (~r2_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_10, c_154])).
% 2.12/1.28  tff(c_162, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_2, c_159])).
% 2.12/1.28  tff(c_165, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_98, c_162])).
% 2.12/1.28  tff(c_168, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_14, c_165])).
% 2.12/1.28  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_80, c_168])).
% 2.12/1.28  tff(c_173, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_42])).
% 2.12/1.28  tff(c_174, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_42])).
% 2.12/1.28  tff(c_205, plain, (![A_100, B_101, C_102]: (k2_relset_1(A_100, B_101, C_102)=k2_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.28  tff(c_208, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_205])).
% 2.12/1.28  tff(c_210, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_208])).
% 2.12/1.28  tff(c_235, plain, (![A_105, C_106]: (r2_hidden(k4_tarski('#skF_5'(A_105, k2_relat_1(A_105), C_106), C_106), A_105) | ~r2_hidden(C_106, k2_relat_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.28  tff(c_38, plain, (![E_45]: (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski(E_45, '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.12/1.28  tff(c_185, plain, (![E_45]: (~r2_hidden(k4_tarski(E_45, '#skF_10'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_38])).
% 2.12/1.28  tff(c_242, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_235, c_185])).
% 2.12/1.28  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_210, c_242])).
% 2.12/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.28  
% 2.12/1.28  Inference rules
% 2.12/1.28  ----------------------
% 2.12/1.28  #Ref     : 0
% 2.12/1.28  #Sup     : 37
% 2.12/1.28  #Fact    : 0
% 2.12/1.28  #Define  : 0
% 2.12/1.28  #Split   : 3
% 2.12/1.28  #Chain   : 0
% 2.12/1.28  #Close   : 0
% 2.12/1.29  
% 2.12/1.29  Ordering : KBO
% 2.12/1.29  
% 2.12/1.29  Simplification rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Subsume      : 4
% 2.12/1.29  #Demod        : 13
% 2.12/1.29  #Tautology    : 15
% 2.12/1.29  #SimpNegUnit  : 3
% 2.12/1.29  #BackRed      : 1
% 2.12/1.29  
% 2.12/1.29  #Partial instantiations: 0
% 2.12/1.29  #Strategies tried      : 1
% 2.12/1.29  
% 2.12/1.29  Timing (in seconds)
% 2.12/1.29  ----------------------
% 2.12/1.29  Preprocessing        : 0.32
% 2.12/1.29  Parsing              : 0.16
% 2.12/1.29  CNF conversion       : 0.03
% 2.12/1.29  Main loop            : 0.19
% 2.12/1.29  Inferencing          : 0.07
% 2.12/1.29  Reduction            : 0.05
% 2.12/1.29  Demodulation         : 0.04
% 2.12/1.29  BG Simplification    : 0.01
% 2.12/1.29  Subsumption          : 0.03
% 2.12/1.29  Abstraction          : 0.01
% 2.12/1.29  MUC search           : 0.00
% 2.12/1.29  Cooper               : 0.00
% 2.12/1.29  Total                : 0.54
% 2.12/1.29  Index Insertion      : 0.00
% 2.12/1.29  Index Deletion       : 0.00
% 2.12/1.29  Index Matching       : 0.00
% 2.12/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
