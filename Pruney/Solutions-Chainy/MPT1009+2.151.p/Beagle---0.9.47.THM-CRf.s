%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:03 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   66 (  83 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 159 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k1_tarski(A),B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
     => ( B != k1_xboole_0
       => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(c_18,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_74,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_83,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_77])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_224,plain,(
    ! [B_71,A_72] :
      ( m1_subset_1(B_71,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_71),A_72)))
      | ~ r1_tarski(k2_relat_1(B_71),A_72)
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( k7_relset_1(A_20,B_21,C_22,D_23) = k9_relat_1(C_22,D_23)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_425,plain,(
    ! [B_117,A_118,D_119] :
      ( k7_relset_1(k1_relat_1(B_117),A_118,B_117,D_119) = k9_relat_1(B_117,D_119)
      | ~ r1_tarski(k2_relat_1(B_117),A_118)
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_224,c_24])).

tff(c_433,plain,(
    ! [B_117,D_119] :
      ( k7_relset_1(k1_relat_1(B_117),k2_relat_1(B_117),B_117,D_119) = k9_relat_1(B_117,D_119)
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_6,c_425])).

tff(c_142,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( m1_subset_1(k7_relset_1(A_55,B_56,C_57,D_58),k1_zfmisc_1(B_56))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_155,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( r1_tarski(k7_relset_1(A_55,B_56,C_57,D_58),B_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(resolution,[status(thm)],[c_142,c_12])).

tff(c_449,plain,(
    ! [B_122,A_123,D_124] :
      ( r1_tarski(k7_relset_1(k1_relat_1(B_122),A_123,B_122,D_124),A_123)
      | ~ r1_tarski(k2_relat_1(B_122),A_123)
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_224,c_155])).

tff(c_467,plain,(
    ! [B_117,D_119] :
      ( r1_tarski(k9_relat_1(B_117,D_119),k2_relat_1(B_117))
      | ~ r1_tarski(k2_relat_1(B_117),k2_relat_1(B_117))
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117)
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_449])).

tff(c_475,plain,(
    ! [B_125,D_126] :
      ( r1_tarski(k9_relat_1(B_125,D_126),k2_relat_1(B_125))
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_467])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_107,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_115,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_107])).

tff(c_332,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_relset_1(k1_tarski(A_98),B_99,C_100) = k1_tarski(k1_funct_1(C_100,A_98))
      | k1_xboole_0 = B_99
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_98),B_99)))
      | ~ v1_funct_2(C_100,k1_tarski(A_98),B_99)
      | ~ v1_funct_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_339,plain,
    ( k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski(k1_funct_1('#skF_4','#skF_1'))
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_332])).

tff(c_347,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_115,c_339])).

tff(c_348,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_347])).

tff(c_168,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( k7_relset_1(A_63,B_64,C_65,D_66) = k9_relat_1(C_65,D_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_178,plain,(
    ! [D_66] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_66) = k9_relat_1('#skF_4',D_66) ),
    inference(resolution,[status(thm)],[c_38,c_168])).

tff(c_34,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_189,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_34])).

tff(c_350,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_189])).

tff(c_478,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_475,c_350])).

tff(c_487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_42,c_478])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:07:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.34  
% 2.70/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.34  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.70/1.34  
% 2.70/1.34  %Foreground sorts:
% 2.70/1.34  
% 2.70/1.34  
% 2.70/1.34  %Background operators:
% 2.70/1.34  
% 2.70/1.34  
% 2.70/1.34  %Foreground operators:
% 2.70/1.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.70/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.70/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.70/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.70/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.70/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.34  
% 2.70/1.36  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.70/1.36  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.70/1.36  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.70/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.70/1.36  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.70/1.36  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.70/1.36  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.70/1.36  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.70/1.36  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.70/1.36  tff(f_83, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 2.70/1.36  tff(c_18, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.70/1.36  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.70/1.36  tff(c_74, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.70/1.36  tff(c_77, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_74])).
% 2.70/1.36  tff(c_83, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_77])).
% 2.70/1.36  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.70/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.36  tff(c_224, plain, (![B_71, A_72]: (m1_subset_1(B_71, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_71), A_72))) | ~r1_tarski(k2_relat_1(B_71), A_72) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.70/1.36  tff(c_24, plain, (![A_20, B_21, C_22, D_23]: (k7_relset_1(A_20, B_21, C_22, D_23)=k9_relat_1(C_22, D_23) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.36  tff(c_425, plain, (![B_117, A_118, D_119]: (k7_relset_1(k1_relat_1(B_117), A_118, B_117, D_119)=k9_relat_1(B_117, D_119) | ~r1_tarski(k2_relat_1(B_117), A_118) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_224, c_24])).
% 2.70/1.36  tff(c_433, plain, (![B_117, D_119]: (k7_relset_1(k1_relat_1(B_117), k2_relat_1(B_117), B_117, D_119)=k9_relat_1(B_117, D_119) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_6, c_425])).
% 2.70/1.36  tff(c_142, plain, (![A_55, B_56, C_57, D_58]: (m1_subset_1(k7_relset_1(A_55, B_56, C_57, D_58), k1_zfmisc_1(B_56)) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.70/1.36  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.70/1.36  tff(c_155, plain, (![A_55, B_56, C_57, D_58]: (r1_tarski(k7_relset_1(A_55, B_56, C_57, D_58), B_56) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(resolution, [status(thm)], [c_142, c_12])).
% 2.70/1.36  tff(c_449, plain, (![B_122, A_123, D_124]: (r1_tarski(k7_relset_1(k1_relat_1(B_122), A_123, B_122, D_124), A_123) | ~r1_tarski(k2_relat_1(B_122), A_123) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_224, c_155])).
% 2.70/1.36  tff(c_467, plain, (![B_117, D_119]: (r1_tarski(k9_relat_1(B_117, D_119), k2_relat_1(B_117)) | ~r1_tarski(k2_relat_1(B_117), k2_relat_1(B_117)) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_433, c_449])).
% 2.70/1.36  tff(c_475, plain, (![B_125, D_126]: (r1_tarski(k9_relat_1(B_125, D_126), k2_relat_1(B_125)) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_467])).
% 2.70/1.36  tff(c_36, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.70/1.36  tff(c_40, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.70/1.36  tff(c_107, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.36  tff(c_115, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_107])).
% 2.70/1.36  tff(c_332, plain, (![A_98, B_99, C_100]: (k2_relset_1(k1_tarski(A_98), B_99, C_100)=k1_tarski(k1_funct_1(C_100, A_98)) | k1_xboole_0=B_99 | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_98), B_99))) | ~v1_funct_2(C_100, k1_tarski(A_98), B_99) | ~v1_funct_1(C_100))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.36  tff(c_339, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski(k1_funct_1('#skF_4', '#skF_1')) | k1_xboole_0='#skF_2' | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_332])).
% 2.70/1.36  tff(c_347, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_115, c_339])).
% 2.70/1.36  tff(c_348, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_347])).
% 2.70/1.36  tff(c_168, plain, (![A_63, B_64, C_65, D_66]: (k7_relset_1(A_63, B_64, C_65, D_66)=k9_relat_1(C_65, D_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.36  tff(c_178, plain, (![D_66]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_66)=k9_relat_1('#skF_4', D_66))), inference(resolution, [status(thm)], [c_38, c_168])).
% 2.70/1.36  tff(c_34, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.70/1.36  tff(c_189, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_34])).
% 2.70/1.36  tff(c_350, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_189])).
% 2.70/1.36  tff(c_478, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_475, c_350])).
% 2.70/1.36  tff(c_487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_42, c_478])).
% 2.70/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.36  
% 2.70/1.36  Inference rules
% 2.70/1.36  ----------------------
% 2.70/1.36  #Ref     : 0
% 2.70/1.36  #Sup     : 98
% 2.70/1.36  #Fact    : 0
% 2.70/1.36  #Define  : 0
% 2.70/1.36  #Split   : 2
% 2.70/1.36  #Chain   : 0
% 2.70/1.36  #Close   : 0
% 2.70/1.36  
% 2.70/1.36  Ordering : KBO
% 2.70/1.36  
% 2.70/1.36  Simplification rules
% 2.70/1.36  ----------------------
% 2.70/1.36  #Subsume      : 8
% 2.70/1.36  #Demod        : 31
% 2.70/1.36  #Tautology    : 30
% 2.70/1.36  #SimpNegUnit  : 1
% 2.70/1.36  #BackRed      : 3
% 2.70/1.36  
% 2.70/1.36  #Partial instantiations: 0
% 2.70/1.36  #Strategies tried      : 1
% 2.70/1.36  
% 2.70/1.36  Timing (in seconds)
% 2.70/1.36  ----------------------
% 2.70/1.36  Preprocessing        : 0.31
% 2.70/1.36  Parsing              : 0.16
% 2.70/1.36  CNF conversion       : 0.02
% 2.70/1.36  Main loop            : 0.30
% 2.70/1.36  Inferencing          : 0.11
% 2.70/1.36  Reduction            : 0.09
% 2.70/1.36  Demodulation         : 0.06
% 2.70/1.36  BG Simplification    : 0.02
% 2.70/1.36  Subsumption          : 0.06
% 2.70/1.36  Abstraction          : 0.02
% 2.70/1.36  MUC search           : 0.00
% 2.70/1.36  Cooper               : 0.00
% 2.70/1.36  Total                : 0.64
% 2.70/1.36  Index Insertion      : 0.00
% 2.70/1.36  Index Deletion       : 0.00
% 2.70/1.36  Index Matching       : 0.00
% 2.70/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
