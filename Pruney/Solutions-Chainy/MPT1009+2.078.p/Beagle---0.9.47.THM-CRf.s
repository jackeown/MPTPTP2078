%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:53 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 335 expanded)
%              Number of leaves         :   40 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  113 ( 763 expanded)
%              Number of equality atoms :   42 ( 239 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_130,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_143,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_130])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_224,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_237,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_224])).

tff(c_423,plain,(
    ! [B_131,A_132,C_133] :
      ( k1_xboole_0 = B_131
      | k1_relset_1(A_132,B_131,C_133) = A_132
      | ~ v1_funct_2(C_133,A_132,B_131)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_430,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_423])).

tff(c_438,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_237,c_430])).

tff(c_439,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_438])).

tff(c_22,plain,(
    ! [A_15,B_17] :
      ( k9_relat_1(A_15,k1_tarski(B_17)) = k11_relat_1(A_15,B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_566,plain,(
    ! [A_145] :
      ( k9_relat_1(A_145,k1_relat_1('#skF_4')) = k11_relat_1(A_145,'#skF_1')
      | ~ v1_relat_1(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_22])).

tff(c_26,plain,(
    ! [A_20] :
      ( k9_relat_1(A_20,k1_relat_1(A_20)) = k2_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_576,plain,
    ( k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_26])).

tff(c_589,plain,(
    k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_143,c_576])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,k1_relat_1(B_22))
      | k11_relat_1(B_22,A_21) = k1_xboole_0
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_333,plain,(
    ! [B_107,A_108] :
      ( k1_tarski(k1_funct_1(B_107,A_108)) = k11_relat_1(B_107,A_108)
      | ~ r2_hidden(A_108,k1_relat_1(B_107))
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_620,plain,(
    ! [B_148,A_149] :
      ( k1_tarski(k1_funct_1(B_148,A_149)) = k11_relat_1(B_148,A_149)
      | ~ v1_funct_1(B_148)
      | k11_relat_1(B_148,A_149) = k1_xboole_0
      | ~ v1_relat_1(B_148) ) ),
    inference(resolution,[status(thm)],[c_28,c_333])).

tff(c_279,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k7_relset_1(A_93,B_94,C_95,D_96) = k9_relat_1(C_95,D_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_289,plain,(
    ! [D_96] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_96) = k9_relat_1('#skF_4',D_96) ),
    inference(resolution,[status(thm)],[c_56,c_279])).

tff(c_52,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_300,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_52])).

tff(c_626,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_300])).

tff(c_635,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_589,c_60,c_589,c_626])).

tff(c_637,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_635])).

tff(c_640,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_637])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_640])).

tff(c_645,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_101,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [B_19,A_18] :
      ( k9_relat_1(B_19,A_18) = k2_relat_1(B_19)
      | ~ r1_tarski(k2_relat_1(B_19),k9_relat_1(B_19,A_18))
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_24,c_101])).

tff(c_674,plain,(
    ! [A_18] :
      ( k9_relat_1('#skF_4',A_18) = k2_relat_1('#skF_4')
      | ~ r1_tarski(k1_xboole_0,k9_relat_1('#skF_4',A_18))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_110])).

tff(c_686,plain,(
    ! [A_18] : k9_relat_1('#skF_4',A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_93,c_645,c_674])).

tff(c_737,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_300])).

tff(c_740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/2.03  
% 3.70/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/2.04  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.85/2.04  
% 3.85/2.04  %Foreground sorts:
% 3.85/2.04  
% 3.85/2.04  
% 3.85/2.04  %Background operators:
% 3.85/2.04  
% 3.85/2.04  
% 3.85/2.04  %Foreground operators:
% 3.85/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/2.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.85/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/2.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.85/2.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.85/2.04  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.85/2.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.85/2.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.85/2.04  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.85/2.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.85/2.04  tff('#skF_2', type, '#skF_2': $i).
% 3.85/2.04  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.85/2.04  tff('#skF_3', type, '#skF_3': $i).
% 3.85/2.04  tff('#skF_1', type, '#skF_1': $i).
% 3.85/2.04  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.85/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/2.04  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.85/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.85/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/2.04  tff('#skF_4', type, '#skF_4': $i).
% 3.85/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/2.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.85/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/2.04  
% 3.90/2.06  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.90/2.06  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.90/2.06  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.90/2.06  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.90/2.06  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.90/2.06  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.90/2.06  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.90/2.06  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.90/2.06  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.90/2.06  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.90/2.06  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.90/2.06  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.90/2.06  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.90/2.06  tff(c_14, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.90/2.06  tff(c_85, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.90/2.06  tff(c_93, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(resolution, [status(thm)], [c_14, c_85])).
% 3.90/2.06  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.90/2.06  tff(c_130, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.90/2.06  tff(c_143, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_130])).
% 3.90/2.06  tff(c_24, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.90/2.06  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.90/2.06  tff(c_58, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.90/2.06  tff(c_224, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.90/2.06  tff(c_237, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_224])).
% 3.90/2.06  tff(c_423, plain, (![B_131, A_132, C_133]: (k1_xboole_0=B_131 | k1_relset_1(A_132, B_131, C_133)=A_132 | ~v1_funct_2(C_133, A_132, B_131) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.90/2.06  tff(c_430, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_56, c_423])).
% 3.90/2.06  tff(c_438, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_237, c_430])).
% 3.90/2.06  tff(c_439, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_438])).
% 3.90/2.06  tff(c_22, plain, (![A_15, B_17]: (k9_relat_1(A_15, k1_tarski(B_17))=k11_relat_1(A_15, B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.90/2.06  tff(c_566, plain, (![A_145]: (k9_relat_1(A_145, k1_relat_1('#skF_4'))=k11_relat_1(A_145, '#skF_1') | ~v1_relat_1(A_145))), inference(superposition, [status(thm), theory('equality')], [c_439, c_22])).
% 3.90/2.06  tff(c_26, plain, (![A_20]: (k9_relat_1(A_20, k1_relat_1(A_20))=k2_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.90/2.06  tff(c_576, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_566, c_26])).
% 3.90/2.06  tff(c_589, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_143, c_576])).
% 3.90/2.06  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.90/2.06  tff(c_28, plain, (![A_21, B_22]: (r2_hidden(A_21, k1_relat_1(B_22)) | k11_relat_1(B_22, A_21)=k1_xboole_0 | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.90/2.06  tff(c_333, plain, (![B_107, A_108]: (k1_tarski(k1_funct_1(B_107, A_108))=k11_relat_1(B_107, A_108) | ~r2_hidden(A_108, k1_relat_1(B_107)) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.90/2.06  tff(c_620, plain, (![B_148, A_149]: (k1_tarski(k1_funct_1(B_148, A_149))=k11_relat_1(B_148, A_149) | ~v1_funct_1(B_148) | k11_relat_1(B_148, A_149)=k1_xboole_0 | ~v1_relat_1(B_148))), inference(resolution, [status(thm)], [c_28, c_333])).
% 3.90/2.06  tff(c_279, plain, (![A_93, B_94, C_95, D_96]: (k7_relset_1(A_93, B_94, C_95, D_96)=k9_relat_1(C_95, D_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.90/2.06  tff(c_289, plain, (![D_96]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_96)=k9_relat_1('#skF_4', D_96))), inference(resolution, [status(thm)], [c_56, c_279])).
% 3.90/2.06  tff(c_52, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.90/2.06  tff(c_300, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_52])).
% 3.90/2.06  tff(c_626, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_1')) | ~v1_funct_1('#skF_4') | k11_relat_1('#skF_4', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_620, c_300])).
% 3.90/2.06  tff(c_635, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_143, c_589, c_60, c_589, c_626])).
% 3.90/2.06  tff(c_637, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_635])).
% 3.90/2.06  tff(c_640, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_637])).
% 3.90/2.06  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_640])).
% 3.90/2.06  tff(c_645, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_635])).
% 3.90/2.06  tff(c_101, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/2.06  tff(c_110, plain, (![B_19, A_18]: (k9_relat_1(B_19, A_18)=k2_relat_1(B_19) | ~r1_tarski(k2_relat_1(B_19), k9_relat_1(B_19, A_18)) | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_24, c_101])).
% 3.90/2.06  tff(c_674, plain, (![A_18]: (k9_relat_1('#skF_4', A_18)=k2_relat_1('#skF_4') | ~r1_tarski(k1_xboole_0, k9_relat_1('#skF_4', A_18)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_645, c_110])).
% 3.90/2.06  tff(c_686, plain, (![A_18]: (k9_relat_1('#skF_4', A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_93, c_645, c_674])).
% 3.90/2.06  tff(c_737, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_686, c_300])).
% 3.90/2.06  tff(c_740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_737])).
% 3.90/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/2.06  
% 3.90/2.06  Inference rules
% 3.90/2.06  ----------------------
% 3.90/2.06  #Ref     : 0
% 3.90/2.06  #Sup     : 136
% 3.90/2.06  #Fact    : 0
% 3.90/2.06  #Define  : 0
% 3.90/2.06  #Split   : 3
% 3.90/2.06  #Chain   : 0
% 3.90/2.06  #Close   : 0
% 3.90/2.06  
% 3.90/2.06  Ordering : KBO
% 3.90/2.06  
% 3.90/2.06  Simplification rules
% 3.90/2.06  ----------------------
% 3.90/2.06  #Subsume      : 8
% 3.90/2.06  #Demod        : 99
% 3.90/2.06  #Tautology    : 78
% 3.90/2.06  #SimpNegUnit  : 7
% 3.90/2.06  #BackRed      : 11
% 3.90/2.06  
% 3.90/2.06  #Partial instantiations: 0
% 3.90/2.06  #Strategies tried      : 1
% 3.90/2.06  
% 3.90/2.06  Timing (in seconds)
% 3.90/2.06  ----------------------
% 3.90/2.07  Preprocessing        : 0.53
% 3.90/2.07  Parsing              : 0.27
% 3.90/2.07  CNF conversion       : 0.04
% 3.90/2.07  Main loop            : 0.57
% 3.90/2.07  Inferencing          : 0.21
% 3.90/2.07  Reduction            : 0.18
% 3.90/2.07  Demodulation         : 0.13
% 3.90/2.07  BG Simplification    : 0.03
% 3.90/2.07  Subsumption          : 0.11
% 3.90/2.07  Abstraction          : 0.03
% 3.90/2.07  MUC search           : 0.00
% 3.90/2.07  Cooper               : 0.00
% 3.90/2.07  Total                : 1.16
% 3.90/2.07  Index Insertion      : 0.00
% 3.90/2.07  Index Deletion       : 0.00
% 3.90/2.07  Index Matching       : 0.00
% 3.90/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
