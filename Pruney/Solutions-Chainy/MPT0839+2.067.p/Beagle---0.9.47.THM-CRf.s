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
% DateTime   : Thu Dec  3 10:08:30 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 115 expanded)
%              Number of leaves         :   31 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 214 expanded)
%              Number of equality atoms :   27 (  59 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_32,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_73,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_83,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_73])).

tff(c_88,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_83])).

tff(c_22,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) = k1_xboole_0
      | k1_relat_1(A_17) != k1_xboole_0
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_92,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_22])).

tff(c_94,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_134,plain,(
    ! [C_61,B_62,A_63] :
      ( r2_hidden(C_61,B_62)
      | ~ r2_hidden(C_61,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_157,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_2'(A_67),B_68)
      | ~ r1_tarski(A_67,B_68)
      | k1_xboole_0 = A_67 ) ),
    inference(resolution,[status(thm)],[c_8,c_134])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_169,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1('#skF_2'(A_67),B_68)
      | ~ r1_tarski(A_67,B_68)
      | k1_xboole_0 = A_67 ) ),
    inference(resolution,[status(thm)],[c_157,c_10])).

tff(c_219,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_243,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_219])).

tff(c_57,plain,(
    ! [D_47] :
      ( ~ r2_hidden(D_47,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_47,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_2'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4')
    | k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_57])).

tff(c_102,plain,(
    ~ m1_subset_1('#skF_2'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_245,plain,(
    ~ m1_subset_1('#skF_2'(k1_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_102])).

tff(c_253,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_169,c_245])).

tff(c_256,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_253])).

tff(c_461,plain,(
    ! [A_108,B_109,C_110] :
      ( m1_subset_1(k1_relset_1(A_108,B_109,C_110),k1_zfmisc_1(A_108))
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_481,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_461])).

tff(c_487,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_481])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_493,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_487,c_12])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_493])).

tff(c_499,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_633,plain,(
    ! [A_130,B_131,C_132] :
      ( k1_relset_1(A_130,B_131,C_132) = k1_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_652,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_633])).

tff(c_658,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_652])).

tff(c_660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_658])).

tff(c_661,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_890,plain,(
    ! [A_164,B_165,C_166] :
      ( k2_relset_1(A_164,B_165,C_166) = k2_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_909,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_890])).

tff(c_915,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_909])).

tff(c_917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_915])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.61  
% 2.88/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.61  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.23/1.61  
% 3.23/1.61  %Foreground sorts:
% 3.23/1.61  
% 3.23/1.61  
% 3.23/1.61  %Background operators:
% 3.23/1.61  
% 3.23/1.61  
% 3.23/1.61  %Foreground operators:
% 3.23/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.23/1.61  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.23/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.23/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.23/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.62  
% 3.23/1.63  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 3.23/1.63  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.23/1.63  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.23/1.63  tff(f_63, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.23/1.63  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.23/1.63  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.23/1.63  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.23/1.63  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.23/1.63  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.23/1.63  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.23/1.63  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.23/1.63  tff(c_32, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.23/1.63  tff(c_18, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.23/1.63  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.23/1.63  tff(c_73, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.63  tff(c_83, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_73])).
% 3.23/1.63  tff(c_88, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_83])).
% 3.23/1.63  tff(c_22, plain, (![A_17]: (k2_relat_1(A_17)=k1_xboole_0 | k1_relat_1(A_17)!=k1_xboole_0 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.23/1.63  tff(c_92, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_22])).
% 3.23/1.63  tff(c_94, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_92])).
% 3.23/1.63  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.23/1.63  tff(c_134, plain, (![C_61, B_62, A_63]: (r2_hidden(C_61, B_62) | ~r2_hidden(C_61, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.63  tff(c_157, plain, (![A_67, B_68]: (r2_hidden('#skF_2'(A_67), B_68) | ~r1_tarski(A_67, B_68) | k1_xboole_0=A_67)), inference(resolution, [status(thm)], [c_8, c_134])).
% 3.23/1.63  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.23/1.63  tff(c_169, plain, (![A_67, B_68]: (m1_subset_1('#skF_2'(A_67), B_68) | ~r1_tarski(A_67, B_68) | k1_xboole_0=A_67)), inference(resolution, [status(thm)], [c_157, c_10])).
% 3.23/1.63  tff(c_219, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.23/1.63  tff(c_243, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_219])).
% 3.23/1.63  tff(c_57, plain, (![D_47]: (~r2_hidden(D_47, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_47, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.23/1.63  tff(c_62, plain, (~m1_subset_1('#skF_2'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4') | k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_57])).
% 3.23/1.63  tff(c_102, plain, (~m1_subset_1('#skF_2'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 3.23/1.63  tff(c_245, plain, (~m1_subset_1('#skF_2'(k1_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_102])).
% 3.23/1.63  tff(c_253, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_169, c_245])).
% 3.23/1.63  tff(c_256, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_94, c_253])).
% 3.23/1.63  tff(c_461, plain, (![A_108, B_109, C_110]: (m1_subset_1(k1_relset_1(A_108, B_109, C_110), k1_zfmisc_1(A_108)) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.23/1.63  tff(c_481, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_243, c_461])).
% 3.23/1.63  tff(c_487, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_481])).
% 3.23/1.63  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.23/1.63  tff(c_493, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_487, c_12])).
% 3.23/1.63  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_256, c_493])).
% 3.23/1.63  tff(c_499, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 3.23/1.63  tff(c_633, plain, (![A_130, B_131, C_132]: (k1_relset_1(A_130, B_131, C_132)=k1_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.23/1.63  tff(c_652, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_633])).
% 3.23/1.63  tff(c_658, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_499, c_652])).
% 3.23/1.63  tff(c_660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_658])).
% 3.23/1.63  tff(c_661, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_92])).
% 3.23/1.63  tff(c_890, plain, (![A_164, B_165, C_166]: (k2_relset_1(A_164, B_165, C_166)=k2_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.63  tff(c_909, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_890])).
% 3.23/1.63  tff(c_915, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_661, c_909])).
% 3.23/1.63  tff(c_917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_915])).
% 3.23/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.63  
% 3.23/1.63  Inference rules
% 3.23/1.63  ----------------------
% 3.23/1.63  #Ref     : 0
% 3.23/1.63  #Sup     : 175
% 3.23/1.63  #Fact    : 0
% 3.23/1.63  #Define  : 0
% 3.23/1.63  #Split   : 5
% 3.23/1.63  #Chain   : 0
% 3.23/1.63  #Close   : 0
% 3.23/1.63  
% 3.23/1.63  Ordering : KBO
% 3.23/1.63  
% 3.23/1.63  Simplification rules
% 3.23/1.63  ----------------------
% 3.23/1.63  #Subsume      : 12
% 3.23/1.63  #Demod        : 27
% 3.23/1.63  #Tautology    : 37
% 3.23/1.63  #SimpNegUnit  : 8
% 3.23/1.63  #BackRed      : 8
% 3.23/1.63  
% 3.23/1.63  #Partial instantiations: 0
% 3.23/1.63  #Strategies tried      : 1
% 3.23/1.63  
% 3.23/1.63  Timing (in seconds)
% 3.23/1.63  ----------------------
% 3.23/1.63  Preprocessing        : 0.39
% 3.23/1.63  Parsing              : 0.19
% 3.23/1.63  CNF conversion       : 0.04
% 3.23/1.63  Main loop            : 0.42
% 3.23/1.63  Inferencing          : 0.17
% 3.23/1.63  Reduction            : 0.11
% 3.23/1.63  Demodulation         : 0.08
% 3.23/1.63  BG Simplification    : 0.02
% 3.23/1.63  Subsumption          : 0.07
% 3.23/1.63  Abstraction          : 0.03
% 3.23/1.63  MUC search           : 0.00
% 3.23/1.63  Cooper               : 0.00
% 3.23/1.63  Total                : 0.84
% 3.23/1.63  Index Insertion      : 0.00
% 3.23/1.63  Index Deletion       : 0.00
% 3.23/1.63  Index Matching       : 0.00
% 3.23/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
