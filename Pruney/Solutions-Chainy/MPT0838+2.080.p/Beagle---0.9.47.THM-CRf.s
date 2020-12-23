%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:20 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 139 expanded)
%              Number of leaves         :   31 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 268 expanded)
%              Number of equality atoms :   37 (  75 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_32,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_73,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_83,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
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

tff(c_543,plain,(
    ! [A_114] :
      ( k1_relat_1(A_114) = k1_xboole_0
      | k2_relat_1(A_114) != k1_xboole_0
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_546,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_543])).

tff(c_552,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_546])).

tff(c_103,plain,(
    ! [A_57] :
      ( k1_relat_1(A_57) = k1_xboole_0
      | k2_relat_1(A_57) != k1_xboole_0
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_106,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_103])).

tff(c_112,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_106])).

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

tff(c_353,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_relset_1(A_98,B_99,C_100) = k2_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_382,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_353])).

tff(c_57,plain,(
    ! [D_47] :
      ( ~ r2_hidden(D_47,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_47,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_57])).

tff(c_102,plain,(
    ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_385,plain,(
    ~ m1_subset_1('#skF_2'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_102])).

tff(c_393,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_169,c_385])).

tff(c_396,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_393])).

tff(c_473,plain,(
    ! [A_107,B_108,C_109] :
      ( m1_subset_1(k2_relset_1(A_107,B_108,C_109),k1_zfmisc_1(B_108))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_490,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_473])).

tff(c_496,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_490])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_502,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_496,c_12])).

tff(c_507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_396,c_502])).

tff(c_508,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_712,plain,(
    ! [A_140,B_141,C_142] :
      ( k2_relset_1(A_140,B_141,C_142) = k2_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_731,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_712])).

tff(c_737,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_731])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_552,c_737])).

tff(c_741,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_884,plain,(
    ! [A_167,B_168,C_169] :
      ( k1_relset_1(A_167,B_168,C_169) = k1_relat_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_903,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_884])).

tff(c_909,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_903])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.39  
% 2.79/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.39  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.79/1.39  
% 2.79/1.39  %Foreground sorts:
% 2.79/1.39  
% 2.79/1.39  
% 2.79/1.39  %Background operators:
% 2.79/1.39  
% 2.79/1.39  
% 2.79/1.39  %Foreground operators:
% 2.79/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.79/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.79/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.79/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.39  
% 2.79/1.41  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.79/1.41  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.79/1.41  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.79/1.41  tff(f_63, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.79/1.41  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.79/1.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.79/1.41  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.79/1.41  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.79/1.41  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.79/1.41  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.79/1.41  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.79/1.41  tff(c_32, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.79/1.41  tff(c_18, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.41  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.79/1.41  tff(c_73, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.79/1.41  tff(c_83, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_73])).
% 2.79/1.41  tff(c_88, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_83])).
% 2.79/1.41  tff(c_22, plain, (![A_17]: (k2_relat_1(A_17)=k1_xboole_0 | k1_relat_1(A_17)!=k1_xboole_0 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.79/1.41  tff(c_92, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_22])).
% 2.79/1.41  tff(c_94, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_92])).
% 2.79/1.41  tff(c_543, plain, (![A_114]: (k1_relat_1(A_114)=k1_xboole_0 | k2_relat_1(A_114)!=k1_xboole_0 | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.79/1.41  tff(c_546, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_543])).
% 2.79/1.41  tff(c_552, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_94, c_546])).
% 2.79/1.41  tff(c_103, plain, (![A_57]: (k1_relat_1(A_57)=k1_xboole_0 | k2_relat_1(A_57)!=k1_xboole_0 | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.79/1.41  tff(c_106, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_103])).
% 2.79/1.41  tff(c_112, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_94, c_106])).
% 2.79/1.41  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.79/1.41  tff(c_134, plain, (![C_61, B_62, A_63]: (r2_hidden(C_61, B_62) | ~r2_hidden(C_61, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.41  tff(c_157, plain, (![A_67, B_68]: (r2_hidden('#skF_2'(A_67), B_68) | ~r1_tarski(A_67, B_68) | k1_xboole_0=A_67)), inference(resolution, [status(thm)], [c_8, c_134])).
% 2.79/1.41  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.79/1.41  tff(c_169, plain, (![A_67, B_68]: (m1_subset_1('#skF_2'(A_67), B_68) | ~r1_tarski(A_67, B_68) | k1_xboole_0=A_67)), inference(resolution, [status(thm)], [c_157, c_10])).
% 2.79/1.41  tff(c_353, plain, (![A_98, B_99, C_100]: (k2_relset_1(A_98, B_99, C_100)=k2_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.79/1.41  tff(c_382, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_353])).
% 2.79/1.41  tff(c_57, plain, (![D_47]: (~r2_hidden(D_47, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_47, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.79/1.41  tff(c_62, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_57])).
% 2.79/1.41  tff(c_102, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 2.79/1.41  tff(c_385, plain, (~m1_subset_1('#skF_2'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_382, c_102])).
% 2.79/1.41  tff(c_393, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_169, c_385])).
% 2.79/1.41  tff(c_396, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_112, c_393])).
% 2.79/1.41  tff(c_473, plain, (![A_107, B_108, C_109]: (m1_subset_1(k2_relset_1(A_107, B_108, C_109), k1_zfmisc_1(B_108)) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.79/1.41  tff(c_490, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_382, c_473])).
% 2.79/1.41  tff(c_496, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_490])).
% 2.79/1.41  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.79/1.41  tff(c_502, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_496, c_12])).
% 2.79/1.41  tff(c_507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_396, c_502])).
% 2.79/1.41  tff(c_508, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 2.79/1.41  tff(c_712, plain, (![A_140, B_141, C_142]: (k2_relset_1(A_140, B_141, C_142)=k2_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.79/1.41  tff(c_731, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_712])).
% 2.79/1.41  tff(c_737, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_508, c_731])).
% 2.79/1.41  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_552, c_737])).
% 2.79/1.41  tff(c_741, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_92])).
% 2.79/1.41  tff(c_884, plain, (![A_167, B_168, C_169]: (k1_relset_1(A_167, B_168, C_169)=k1_relat_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.41  tff(c_903, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_884])).
% 2.79/1.41  tff(c_909, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_741, c_903])).
% 2.79/1.41  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_909])).
% 2.79/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.41  
% 2.79/1.41  Inference rules
% 2.79/1.41  ----------------------
% 2.79/1.41  #Ref     : 0
% 2.79/1.41  #Sup     : 175
% 2.79/1.41  #Fact    : 0
% 2.79/1.41  #Define  : 0
% 2.79/1.41  #Split   : 6
% 2.79/1.41  #Chain   : 0
% 2.79/1.41  #Close   : 0
% 2.79/1.41  
% 2.79/1.41  Ordering : KBO
% 2.79/1.41  
% 2.79/1.41  Simplification rules
% 2.79/1.41  ----------------------
% 2.79/1.41  #Subsume      : 12
% 2.79/1.41  #Demod        : 22
% 2.79/1.41  #Tautology    : 36
% 2.79/1.41  #SimpNegUnit  : 8
% 2.79/1.41  #BackRed      : 7
% 2.79/1.41  
% 2.79/1.41  #Partial instantiations: 0
% 2.79/1.41  #Strategies tried      : 1
% 2.79/1.41  
% 2.79/1.41  Timing (in seconds)
% 2.79/1.41  ----------------------
% 2.79/1.41  Preprocessing        : 0.29
% 2.79/1.41  Parsing              : 0.16
% 2.79/1.41  CNF conversion       : 0.02
% 2.79/1.41  Main loop            : 0.36
% 2.79/1.41  Inferencing          : 0.14
% 2.79/1.41  Reduction            : 0.10
% 2.79/1.41  Demodulation         : 0.07
% 2.79/1.41  BG Simplification    : 0.02
% 2.79/1.41  Subsumption          : 0.06
% 2.79/1.41  Abstraction          : 0.02
% 2.79/1.41  MUC search           : 0.00
% 2.79/1.41  Cooper               : 0.00
% 2.79/1.41  Total                : 0.68
% 2.79/1.41  Index Insertion      : 0.00
% 2.79/1.41  Index Deletion       : 0.00
% 2.79/1.41  Index Matching       : 0.00
% 2.79/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
