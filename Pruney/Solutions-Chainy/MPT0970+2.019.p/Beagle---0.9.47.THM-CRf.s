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
% DateTime   : Thu Dec  3 10:11:21 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 159 expanded)
%              Number of leaves         :   38 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 375 expanded)
%              Number of equality atoms :   25 (  82 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_52,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_84,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_88,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_84])).

tff(c_132,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_136,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_132])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_155,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_159,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_155])).

tff(c_160,plain,(
    k2_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_52])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_62,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_7'(D_34),'#skF_4')
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_60,plain,(
    ! [D_34] :
      ( k1_funct_1('#skF_6','#skF_7'(D_34)) = D_34
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_111,plain,(
    ! [A_55,B_56] :
      ( r2_xboole_0(A_55,B_56)
      | B_56 = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_1'(A_51,B_52),B_52)
      | ~ r2_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,(
    ! [B_52,A_51] :
      ( ~ v1_xboole_0(B_52)
      | ~ r2_xboole_0(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_100,c_14])).

tff(c_127,plain,(
    ! [B_59,A_60] :
      ( ~ v1_xboole_0(B_59)
      | B_59 = A_60
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(resolution,[status(thm)],[c_111,c_109])).

tff(c_147,plain,(
    ! [A_69,B_70] :
      ( ~ v1_xboole_0(A_69)
      | k2_relat_1(B_70) = A_69
      | ~ v5_relat_1(B_70,A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_18,c_127])).

tff(c_150,plain,
    ( ~ v1_xboole_0('#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_136,c_147])).

tff(c_153,plain,
    ( ~ v1_xboole_0('#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_150])).

tff(c_154,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_266,plain,(
    ! [D_114,C_115,A_116,B_117] :
      ( r2_hidden(k1_funct_1(D_114,C_115),k2_relset_1(A_116,B_117,D_114))
      | k1_xboole_0 = B_117
      | ~ r2_hidden(C_115,A_116)
      | ~ m1_subset_1(D_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_2(D_114,A_116,B_117)
      | ~ v1_funct_1(D_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_272,plain,(
    ! [C_115] :
      ( r2_hidden(k1_funct_1('#skF_6',C_115),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_115,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_266])).

tff(c_278,plain,(
    ! [C_115] :
      ( r2_hidden(k1_funct_1('#skF_6',C_115),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_115,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_272])).

tff(c_281,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_290,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_8])).

tff(c_292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_290])).

tff(c_295,plain,(
    ! [C_118] :
      ( r2_hidden(k1_funct_1('#skF_6',C_118),k2_relat_1('#skF_6'))
      | ~ r2_hidden(C_118,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_313,plain,(
    ! [D_121] :
      ( r2_hidden(D_121,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_121),'#skF_4')
      | ~ r2_hidden(D_121,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_295])).

tff(c_318,plain,(
    ! [D_122] :
      ( r2_hidden(D_122,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_122,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_313])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),A_3)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_328,plain,(
    ! [B_123] :
      ( ~ r2_xboole_0(k2_relat_1('#skF_6'),B_123)
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_6'),B_123),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_318,c_10])).

tff(c_333,plain,(
    ~ r2_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_328])).

tff(c_336,plain,
    ( k2_relat_1('#skF_6') = '#skF_5'
    | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_333])).

tff(c_339,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_336])).

tff(c_342,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_339])).

tff(c_346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_136,c_342])).

tff(c_347,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_364,plain,(
    ! [A_124,B_125,C_126] :
      ( k2_relset_1(A_124,B_125,C_126) = k2_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_367,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_364])).

tff(c_369,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_367])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.47  
% 2.83/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.83/1.47  
% 2.83/1.47  %Foreground sorts:
% 2.83/1.47  
% 2.83/1.47  
% 2.83/1.47  %Background operators:
% 2.83/1.47  
% 2.83/1.47  
% 2.83/1.47  %Foreground operators:
% 2.83/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.83/1.47  tff('#skF_7', type, '#skF_7': $i > $i).
% 2.83/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.83/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.83/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.83/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.83/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.83/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.83/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.47  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.83/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.83/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.83/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.83/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.83/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.47  
% 2.83/1.48  tff(f_137, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 2.83/1.48  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.83/1.48  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.83/1.48  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.83/1.48  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.83/1.48  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.83/1.48  tff(f_43, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.83/1.48  tff(f_48, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 2.83/1.48  tff(f_118, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.83/1.48  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.83/1.48  tff(c_52, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.83/1.48  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.83/1.48  tff(c_84, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.83/1.48  tff(c_88, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_84])).
% 2.83/1.48  tff(c_132, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.83/1.48  tff(c_136, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_132])).
% 2.83/1.48  tff(c_18, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.83/1.48  tff(c_155, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.83/1.48  tff(c_159, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_155])).
% 2.83/1.48  tff(c_160, plain, (k2_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_52])).
% 2.83/1.48  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.48  tff(c_12, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.48  tff(c_62, plain, (![D_34]: (r2_hidden('#skF_7'(D_34), '#skF_4') | ~r2_hidden(D_34, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.83/1.48  tff(c_60, plain, (![D_34]: (k1_funct_1('#skF_6', '#skF_7'(D_34))=D_34 | ~r2_hidden(D_34, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.83/1.48  tff(c_111, plain, (![A_55, B_56]: (r2_xboole_0(A_55, B_56) | B_56=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.48  tff(c_100, plain, (![A_51, B_52]: (r2_hidden('#skF_1'(A_51, B_52), B_52) | ~r2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.48  tff(c_14, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.83/1.48  tff(c_109, plain, (![B_52, A_51]: (~v1_xboole_0(B_52) | ~r2_xboole_0(A_51, B_52))), inference(resolution, [status(thm)], [c_100, c_14])).
% 2.83/1.48  tff(c_127, plain, (![B_59, A_60]: (~v1_xboole_0(B_59) | B_59=A_60 | ~r1_tarski(A_60, B_59))), inference(resolution, [status(thm)], [c_111, c_109])).
% 2.83/1.48  tff(c_147, plain, (![A_69, B_70]: (~v1_xboole_0(A_69) | k2_relat_1(B_70)=A_69 | ~v5_relat_1(B_70, A_69) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_18, c_127])).
% 2.83/1.48  tff(c_150, plain, (~v1_xboole_0('#skF_5') | k2_relat_1('#skF_6')='#skF_5' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_136, c_147])).
% 2.83/1.48  tff(c_153, plain, (~v1_xboole_0('#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_150])).
% 2.83/1.48  tff(c_154, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_153])).
% 2.83/1.48  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.83/1.48  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.83/1.48  tff(c_266, plain, (![D_114, C_115, A_116, B_117]: (r2_hidden(k1_funct_1(D_114, C_115), k2_relset_1(A_116, B_117, D_114)) | k1_xboole_0=B_117 | ~r2_hidden(C_115, A_116) | ~m1_subset_1(D_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_2(D_114, A_116, B_117) | ~v1_funct_1(D_114))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.83/1.48  tff(c_272, plain, (![C_115]: (r2_hidden(k1_funct_1('#skF_6', C_115), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_115, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_266])).
% 2.83/1.48  tff(c_278, plain, (![C_115]: (r2_hidden(k1_funct_1('#skF_6', C_115), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_115, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_272])).
% 2.83/1.48  tff(c_281, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_278])).
% 2.83/1.48  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.48  tff(c_290, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_8])).
% 2.83/1.48  tff(c_292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_290])).
% 2.83/1.48  tff(c_295, plain, (![C_118]: (r2_hidden(k1_funct_1('#skF_6', C_118), k2_relat_1('#skF_6')) | ~r2_hidden(C_118, '#skF_4'))), inference(splitRight, [status(thm)], [c_278])).
% 2.83/1.48  tff(c_313, plain, (![D_121]: (r2_hidden(D_121, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_121), '#skF_4') | ~r2_hidden(D_121, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_295])).
% 2.83/1.48  tff(c_318, plain, (![D_122]: (r2_hidden(D_122, k2_relat_1('#skF_6')) | ~r2_hidden(D_122, '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_313])).
% 2.83/1.48  tff(c_10, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), A_3) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.48  tff(c_328, plain, (![B_123]: (~r2_xboole_0(k2_relat_1('#skF_6'), B_123) | ~r2_hidden('#skF_1'(k2_relat_1('#skF_6'), B_123), '#skF_5'))), inference(resolution, [status(thm)], [c_318, c_10])).
% 2.83/1.48  tff(c_333, plain, (~r2_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_12, c_328])).
% 2.83/1.48  tff(c_336, plain, (k2_relat_1('#skF_6')='#skF_5' | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_2, c_333])).
% 2.83/1.48  tff(c_339, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_160, c_336])).
% 2.83/1.48  tff(c_342, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18, c_339])).
% 2.83/1.48  tff(c_346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_136, c_342])).
% 2.83/1.48  tff(c_347, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_153])).
% 2.83/1.48  tff(c_364, plain, (![A_124, B_125, C_126]: (k2_relset_1(A_124, B_125, C_126)=k2_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.83/1.48  tff(c_367, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_364])).
% 2.83/1.48  tff(c_369, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_367])).
% 2.83/1.48  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_369])).
% 2.83/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.48  
% 2.83/1.48  Inference rules
% 2.83/1.48  ----------------------
% 2.83/1.48  #Ref     : 0
% 2.83/1.48  #Sup     : 57
% 2.83/1.48  #Fact    : 0
% 2.83/1.48  #Define  : 0
% 2.83/1.48  #Split   : 6
% 2.83/1.48  #Chain   : 0
% 2.83/1.48  #Close   : 0
% 2.83/1.48  
% 2.83/1.48  Ordering : KBO
% 2.83/1.48  
% 2.83/1.48  Simplification rules
% 2.83/1.48  ----------------------
% 2.83/1.48  #Subsume      : 4
% 2.83/1.48  #Demod        : 28
% 2.83/1.48  #Tautology    : 15
% 2.83/1.48  #SimpNegUnit  : 4
% 2.83/1.48  #BackRed      : 11
% 2.83/1.48  
% 2.83/1.48  #Partial instantiations: 0
% 2.83/1.48  #Strategies tried      : 1
% 2.83/1.48  
% 2.83/1.48  Timing (in seconds)
% 2.83/1.48  ----------------------
% 2.83/1.49  Preprocessing        : 0.34
% 2.83/1.49  Parsing              : 0.19
% 2.83/1.49  CNF conversion       : 0.02
% 2.83/1.49  Main loop            : 0.26
% 2.83/1.49  Inferencing          : 0.10
% 2.83/1.49  Reduction            : 0.07
% 2.83/1.49  Demodulation         : 0.05
% 2.83/1.49  BG Simplification    : 0.02
% 2.83/1.49  Subsumption          : 0.05
% 2.83/1.49  Abstraction          : 0.02
% 2.83/1.49  MUC search           : 0.00
% 2.83/1.49  Cooper               : 0.00
% 2.83/1.49  Total                : 0.64
% 2.83/1.49  Index Insertion      : 0.00
% 2.83/1.49  Index Deletion       : 0.00
% 2.83/1.49  Index Matching       : 0.00
% 2.83/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
