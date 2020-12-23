%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:08 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
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
%$ v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_70,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_70,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_70])).

tff(c_82,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_86,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_82])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_92,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_96,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_92])).

tff(c_42,plain,
    ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_69,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_98,plain,(
    k1_relat_1('#skF_8') != '#skF_7' ),
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
      ( r2_hidden(k4_tarski(D_42,'#skF_9'(D_42)),'#skF_8')
      | ~ r2_hidden(D_42,'#skF_7')
      | k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_131,plain,(
    ! [D_42] :
      ( r2_hidden(k4_tarski(D_42,'#skF_9'(D_42)),'#skF_8')
      | ~ r2_hidden(D_42,'#skF_7')
      | k1_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_48])).

tff(c_133,plain,(
    ! [D_80] :
      ( r2_hidden(k4_tarski(D_80,'#skF_9'(D_80)),'#skF_8')
      | ~ r2_hidden(D_80,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_131])).

tff(c_18,plain,(
    ! [C_23,A_8,D_26] :
      ( r2_hidden(C_23,k1_relat_1(A_8))
      | ~ r2_hidden(k4_tarski(C_23,D_26),A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_138,plain,(
    ! [D_81] :
      ( r2_hidden(D_81,k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_81,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_133,c_18])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),A_3)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_154,plain,(
    ! [B_82] :
      ( ~ r2_xboole_0(k1_relat_1('#skF_8'),B_82)
      | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_8'),B_82),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_138,c_8])).

tff(c_159,plain,(
    ~ r2_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_162,plain,
    ( k1_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2,c_159])).

tff(c_165,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_162])).

tff(c_168,plain,
    ( ~ v4_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_14,c_165])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_86,c_168])).

tff(c_173,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_174,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_205,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_208,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_205])).

tff(c_210,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_208])).

tff(c_235,plain,(
    ! [C_105,A_106] :
      ( r2_hidden(k4_tarski(C_105,'#skF_5'(A_106,k1_relat_1(A_106),C_105)),A_106)
      | ~ r2_hidden(C_105,k1_relat_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    ! [E_45] :
      ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski('#skF_10',E_45),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_185,plain,(
    ! [E_45] : ~ r2_hidden(k4_tarski('#skF_10',E_45),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_38])).

tff(c_242,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_235,c_185])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_210,c_242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.67  
% 2.56/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.68  %$ v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.56/1.68  
% 2.56/1.68  %Foreground sorts:
% 2.56/1.68  
% 2.56/1.68  
% 2.56/1.68  %Background operators:
% 2.56/1.68  
% 2.56/1.68  
% 2.56/1.68  %Foreground operators:
% 2.56/1.68  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.56/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.56/1.68  tff('#skF_7', type, '#skF_7': $i).
% 2.56/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.56/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.68  tff('#skF_10', type, '#skF_10': $i).
% 2.56/1.68  tff('#skF_6', type, '#skF_6': $i).
% 2.56/1.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.56/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.56/1.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.56/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.68  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.56/1.68  tff('#skF_8', type, '#skF_8': $i).
% 2.56/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.56/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.56/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.56/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.56/1.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.56/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.68  
% 2.56/1.70  tff(f_83, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 2.56/1.70  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.56/1.70  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.56/1.70  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.56/1.70  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.56/1.70  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.56/1.70  tff(f_42, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.56/1.70  tff(f_56, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.56/1.70  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.70  tff(c_70, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.56/1.70  tff(c_74, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_70])).
% 2.56/1.70  tff(c_82, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.70  tff(c_86, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_36, c_82])).
% 2.56/1.70  tff(c_14, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.56/1.70  tff(c_92, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.56/1.70  tff(c_96, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_92])).
% 2.56/1.70  tff(c_42, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.70  tff(c_69, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_42])).
% 2.56/1.70  tff(c_98, plain, (k1_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_69])).
% 2.56/1.70  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.56/1.70  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.70  tff(c_48, plain, (![D_42]: (r2_hidden(k4_tarski(D_42, '#skF_9'(D_42)), '#skF_8') | ~r2_hidden(D_42, '#skF_7') | k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.70  tff(c_131, plain, (![D_42]: (r2_hidden(k4_tarski(D_42, '#skF_9'(D_42)), '#skF_8') | ~r2_hidden(D_42, '#skF_7') | k1_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_48])).
% 2.56/1.70  tff(c_133, plain, (![D_80]: (r2_hidden(k4_tarski(D_80, '#skF_9'(D_80)), '#skF_8') | ~r2_hidden(D_80, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_98, c_131])).
% 2.56/1.70  tff(c_18, plain, (![C_23, A_8, D_26]: (r2_hidden(C_23, k1_relat_1(A_8)) | ~r2_hidden(k4_tarski(C_23, D_26), A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.70  tff(c_138, plain, (![D_81]: (r2_hidden(D_81, k1_relat_1('#skF_8')) | ~r2_hidden(D_81, '#skF_7'))), inference(resolution, [status(thm)], [c_133, c_18])).
% 2.56/1.70  tff(c_8, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), A_3) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.70  tff(c_154, plain, (![B_82]: (~r2_xboole_0(k1_relat_1('#skF_8'), B_82) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_8'), B_82), '#skF_7'))), inference(resolution, [status(thm)], [c_138, c_8])).
% 2.56/1.70  tff(c_159, plain, (~r2_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_10, c_154])).
% 2.56/1.70  tff(c_162, plain, (k1_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_2, c_159])).
% 2.56/1.70  tff(c_165, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_98, c_162])).
% 2.56/1.70  tff(c_168, plain, (~v4_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_14, c_165])).
% 2.56/1.70  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_86, c_168])).
% 2.56/1.70  tff(c_173, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_42])).
% 2.56/1.70  tff(c_174, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_42])).
% 2.56/1.70  tff(c_205, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.56/1.70  tff(c_208, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_205])).
% 2.56/1.70  tff(c_210, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_208])).
% 2.56/1.70  tff(c_235, plain, (![C_105, A_106]: (r2_hidden(k4_tarski(C_105, '#skF_5'(A_106, k1_relat_1(A_106), C_105)), A_106) | ~r2_hidden(C_105, k1_relat_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.70  tff(c_38, plain, (![E_45]: (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski('#skF_10', E_45), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.70  tff(c_185, plain, (![E_45]: (~r2_hidden(k4_tarski('#skF_10', E_45), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_38])).
% 2.56/1.70  tff(c_242, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_235, c_185])).
% 2.56/1.70  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_210, c_242])).
% 2.56/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.70  
% 2.56/1.70  Inference rules
% 2.56/1.70  ----------------------
% 2.56/1.70  #Ref     : 0
% 2.56/1.70  #Sup     : 37
% 2.56/1.70  #Fact    : 0
% 2.56/1.70  #Define  : 0
% 2.56/1.70  #Split   : 3
% 2.56/1.70  #Chain   : 0
% 2.56/1.70  #Close   : 0
% 2.56/1.70  
% 2.56/1.70  Ordering : KBO
% 2.56/1.70  
% 2.56/1.70  Simplification rules
% 2.56/1.70  ----------------------
% 2.56/1.70  #Subsume      : 4
% 2.56/1.70  #Demod        : 13
% 2.56/1.70  #Tautology    : 15
% 2.56/1.70  #SimpNegUnit  : 3
% 2.56/1.70  #BackRed      : 1
% 2.56/1.70  
% 2.56/1.70  #Partial instantiations: 0
% 2.56/1.70  #Strategies tried      : 1
% 2.56/1.70  
% 2.56/1.70  Timing (in seconds)
% 2.56/1.70  ----------------------
% 2.56/1.71  Preprocessing        : 0.49
% 2.56/1.71  Parsing              : 0.24
% 2.56/1.71  CNF conversion       : 0.04
% 2.56/1.71  Main loop            : 0.31
% 2.56/1.71  Inferencing          : 0.12
% 2.56/1.71  Reduction            : 0.08
% 2.56/1.71  Demodulation         : 0.06
% 2.56/1.71  BG Simplification    : 0.02
% 2.56/1.71  Subsumption          : 0.05
% 2.56/1.71  Abstraction          : 0.02
% 2.56/1.71  MUC search           : 0.00
% 2.56/1.71  Cooper               : 0.00
% 2.56/1.71  Total                : 0.86
% 2.56/1.71  Index Insertion      : 0.00
% 2.56/1.71  Index Deletion       : 0.00
% 2.56/1.71  Index Matching       : 0.00
% 2.56/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
