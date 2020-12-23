%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:08 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 100 expanded)
%              Number of leaves         :   32 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 166 expanded)
%              Number of equality atoms :   20 (  47 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_128,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_132,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_128])).

tff(c_44,plain,
    ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_66,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_141,plain,(
    k1_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_66])).

tff(c_53,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_57,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_94,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_98,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_94])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [D_44] :
      ( r2_hidden(k4_tarski(D_44,'#skF_9'(D_44)),'#skF_8')
      | ~ r2_hidden(D_44,'#skF_7')
      | k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_158,plain,(
    ! [D_44] :
      ( r2_hidden(k4_tarski(D_44,'#skF_9'(D_44)),'#skF_8')
      | ~ r2_hidden(D_44,'#skF_7')
      | k1_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_50])).

tff(c_160,plain,(
    ! [D_88] :
      ( r2_hidden(k4_tarski(D_88,'#skF_9'(D_88)),'#skF_8')
      | ~ r2_hidden(D_88,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_158])).

tff(c_20,plain,(
    ! [C_25,A_10,D_28] :
      ( r2_hidden(C_25,k1_relat_1(A_10))
      | ~ r2_hidden(k4_tarski(C_25,D_28),A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_168,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_89,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_160,c_20])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_275,plain,(
    ! [A_101] :
      ( r1_tarski(A_101,k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_101,k1_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_168,c_4])).

tff(c_285,plain,(
    r1_tarski('#skF_7',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_275])).

tff(c_86,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k1_relat_1(B_67),A_68)
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [B_67,A_68] :
      ( k1_relat_1(B_67) = A_68
      | ~ r1_tarski(A_68,k1_relat_1(B_67))
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_86,c_8])).

tff(c_288,plain,
    ( k1_relat_1('#skF_8') = '#skF_7'
    | ~ v4_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_285,c_93])).

tff(c_295,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_98,c_288])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_295])).

tff(c_298,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_299,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_368,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_371,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_368])).

tff(c_373,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_371])).

tff(c_428,plain,(
    ! [C_135,A_136] :
      ( r2_hidden(k4_tarski(C_135,'#skF_5'(A_136,k1_relat_1(A_136),C_135)),A_136)
      | ~ r2_hidden(C_135,k1_relat_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    ! [E_47] :
      ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski('#skF_10',E_47),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_327,plain,(
    ! [E_47] : ~ r2_hidden(k4_tarski('#skF_10',E_47),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_40])).

tff(c_437,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_428,c_327])).

tff(c_446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_373,c_437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.35  
% 2.31/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.35  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.31/1.35  
% 2.31/1.35  %Foreground sorts:
% 2.31/1.35  
% 2.31/1.35  
% 2.31/1.35  %Background operators:
% 2.31/1.35  
% 2.31/1.35  
% 2.31/1.35  %Foreground operators:
% 2.31/1.35  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.31/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.31/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.31/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.35  tff('#skF_10', type, '#skF_10': $i).
% 2.31/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.35  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.31/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.31/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.31/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.31/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.31/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.31/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.31/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.31/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.35  
% 2.31/1.37  tff(f_79, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 2.31/1.37  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.31/1.37  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.31/1.37  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.31/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.31/1.37  tff(f_52, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.31/1.37  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.31/1.37  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.31/1.37  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.37  tff(c_128, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.37  tff(c_132, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_128])).
% 2.31/1.37  tff(c_44, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.37  tff(c_66, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_44])).
% 2.31/1.37  tff(c_141, plain, (k1_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_66])).
% 2.31/1.37  tff(c_53, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.31/1.37  tff(c_57, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.31/1.37  tff(c_94, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.31/1.37  tff(c_98, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_38, c_94])).
% 2.31/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.37  tff(c_50, plain, (![D_44]: (r2_hidden(k4_tarski(D_44, '#skF_9'(D_44)), '#skF_8') | ~r2_hidden(D_44, '#skF_7') | k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.37  tff(c_158, plain, (![D_44]: (r2_hidden(k4_tarski(D_44, '#skF_9'(D_44)), '#skF_8') | ~r2_hidden(D_44, '#skF_7') | k1_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_50])).
% 2.31/1.37  tff(c_160, plain, (![D_88]: (r2_hidden(k4_tarski(D_88, '#skF_9'(D_88)), '#skF_8') | ~r2_hidden(D_88, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_141, c_158])).
% 2.31/1.37  tff(c_20, plain, (![C_25, A_10, D_28]: (r2_hidden(C_25, k1_relat_1(A_10)) | ~r2_hidden(k4_tarski(C_25, D_28), A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.31/1.37  tff(c_168, plain, (![D_89]: (r2_hidden(D_89, k1_relat_1('#skF_8')) | ~r2_hidden(D_89, '#skF_7'))), inference(resolution, [status(thm)], [c_160, c_20])).
% 2.31/1.37  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.37  tff(c_275, plain, (![A_101]: (r1_tarski(A_101, k1_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_101, k1_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_168, c_4])).
% 2.31/1.37  tff(c_285, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_275])).
% 2.31/1.37  tff(c_86, plain, (![B_67, A_68]: (r1_tarski(k1_relat_1(B_67), A_68) | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.31/1.37  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.31/1.37  tff(c_93, plain, (![B_67, A_68]: (k1_relat_1(B_67)=A_68 | ~r1_tarski(A_68, k1_relat_1(B_67)) | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_86, c_8])).
% 2.31/1.37  tff(c_288, plain, (k1_relat_1('#skF_8')='#skF_7' | ~v4_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_285, c_93])).
% 2.31/1.37  tff(c_295, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_98, c_288])).
% 2.31/1.37  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_295])).
% 2.31/1.37  tff(c_298, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 2.31/1.37  tff(c_299, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_44])).
% 2.31/1.37  tff(c_368, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.37  tff(c_371, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_368])).
% 2.31/1.37  tff(c_373, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_299, c_371])).
% 2.31/1.37  tff(c_428, plain, (![C_135, A_136]: (r2_hidden(k4_tarski(C_135, '#skF_5'(A_136, k1_relat_1(A_136), C_135)), A_136) | ~r2_hidden(C_135, k1_relat_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.31/1.37  tff(c_40, plain, (![E_47]: (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski('#skF_10', E_47), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.37  tff(c_327, plain, (![E_47]: (~r2_hidden(k4_tarski('#skF_10', E_47), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_40])).
% 2.31/1.37  tff(c_437, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_428, c_327])).
% 2.31/1.37  tff(c_446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_298, c_373, c_437])).
% 2.31/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.37  
% 2.31/1.37  Inference rules
% 2.31/1.37  ----------------------
% 2.31/1.37  #Ref     : 0
% 2.31/1.37  #Sup     : 81
% 2.31/1.37  #Fact    : 0
% 2.31/1.37  #Define  : 0
% 2.31/1.37  #Split   : 2
% 2.31/1.37  #Chain   : 0
% 2.31/1.37  #Close   : 0
% 2.31/1.37  
% 2.31/1.37  Ordering : KBO
% 2.31/1.37  
% 2.31/1.37  Simplification rules
% 2.31/1.37  ----------------------
% 2.31/1.37  #Subsume      : 7
% 2.31/1.37  #Demod        : 29
% 2.31/1.37  #Tautology    : 26
% 2.31/1.37  #SimpNegUnit  : 2
% 2.31/1.37  #BackRed      : 1
% 2.31/1.37  
% 2.31/1.37  #Partial instantiations: 0
% 2.31/1.37  #Strategies tried      : 1
% 2.31/1.37  
% 2.31/1.37  Timing (in seconds)
% 2.31/1.37  ----------------------
% 2.31/1.37  Preprocessing        : 0.29
% 2.31/1.37  Parsing              : 0.15
% 2.31/1.37  CNF conversion       : 0.02
% 2.31/1.37  Main loop            : 0.24
% 2.31/1.37  Inferencing          : 0.09
% 2.31/1.37  Reduction            : 0.07
% 2.31/1.37  Demodulation         : 0.05
% 2.31/1.37  BG Simplification    : 0.01
% 2.31/1.37  Subsumption          : 0.05
% 2.31/1.37  Abstraction          : 0.01
% 2.31/1.37  MUC search           : 0.00
% 2.31/1.37  Cooper               : 0.00
% 2.31/1.37  Total                : 0.56
% 2.31/1.37  Index Insertion      : 0.00
% 2.31/1.37  Index Deletion       : 0.00
% 2.31/1.37  Index Matching       : 0.00
% 2.31/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
