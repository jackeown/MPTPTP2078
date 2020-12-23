%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:33 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 196 expanded)
%              Number of leaves         :   33 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  124 ( 506 expanded)
%              Number of equality atoms :   17 (  73 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_70,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_79,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_53,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_62,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_160,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( k7_relset_1(A_90,B_91,C_92,D_93) = k9_relat_1(C_92,D_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_167,plain,(
    ! [D_93] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_93) = k9_relat_1('#skF_5',D_93) ),
    inference(resolution,[status(thm)],[c_38,c_160])).

tff(c_36,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_169,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_36])).

tff(c_18,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_1'(A_8,B_9,C_10),k1_relat_1(C_10))
      | ~ r2_hidden(A_8,k9_relat_1(C_10,B_9))
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_189,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden(k4_tarski('#skF_1'(A_96,B_97,C_98),A_96),C_98)
      | ~ r2_hidden(A_96,k9_relat_1(C_98,B_97))
      | ~ v1_relat_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [C_16,A_14,B_15] :
      ( k1_funct_1(C_16,A_14) = B_15
      | ~ r2_hidden(k4_tarski(A_14,B_15),C_16)
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_245,plain,(
    ! [C_105,A_106,B_107] :
      ( k1_funct_1(C_105,'#skF_1'(A_106,B_107,C_105)) = A_106
      | ~ v1_funct_1(C_105)
      | ~ r2_hidden(A_106,k9_relat_1(C_105,B_107))
      | ~ v1_relat_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_189,c_22])).

tff(c_253,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_245])).

tff(c_261,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_42,c_253])).

tff(c_20,plain,(
    ! [A_14,C_16] :
      ( r2_hidden(k4_tarski(A_14,k1_funct_1(C_16,A_14)),C_16)
      | ~ r2_hidden(A_14,k1_relat_1(C_16))
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_266,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_20])).

tff(c_270,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_42,c_266])).

tff(c_288,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_291,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_288])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_169,c_291])).

tff(c_297,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    ! [A_59,C_60,B_61] :
      ( m1_subset_1(A_59,C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_128,plain,(
    ! [A_59,B_2,A_1] :
      ( m1_subset_1(A_59,B_2)
      | ~ r2_hidden(A_59,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_123])).

tff(c_342,plain,(
    ! [B_114] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),B_114)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_114) ) ),
    inference(resolution,[status(thm)],[c_297,c_128])).

tff(c_346,plain,(
    ! [A_6] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),A_6)
      | ~ v4_relat_1('#skF_5',A_6)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_342])).

tff(c_350,plain,(
    ! [A_115] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),A_115)
      | ~ v4_relat_1('#skF_5',A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_346])).

tff(c_140,plain,(
    ! [A_79,B_80,C_81] :
      ( r2_hidden('#skF_1'(A_79,B_80,C_81),B_80)
      | ~ r2_hidden(A_79,k9_relat_1(C_81,B_80))
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ! [F_31] :
      ( k1_funct_1('#skF_5',F_31) != '#skF_6'
      | ~ r2_hidden(F_31,'#skF_4')
      | ~ m1_subset_1(F_31,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_148,plain,(
    ! [A_79,C_81] :
      ( k1_funct_1('#skF_5','#skF_1'(A_79,'#skF_4',C_81)) != '#skF_6'
      | ~ m1_subset_1('#skF_1'(A_79,'#skF_4',C_81),'#skF_2')
      | ~ r2_hidden(A_79,k9_relat_1(C_81,'#skF_4'))
      | ~ v1_relat_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_140,c_34])).

tff(c_181,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_148])).

tff(c_186,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_181])).

tff(c_220,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_353,plain,(
    ~ v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_350,c_220])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_353])).

tff(c_380,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_405,plain,(
    ! [C_118,A_119,B_120] :
      ( k1_funct_1(C_118,'#skF_1'(A_119,B_120,C_118)) = A_119
      | ~ v1_funct_1(C_118)
      | ~ r2_hidden(A_119,k9_relat_1(C_118,B_120))
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_189,c_22])).

tff(c_413,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_405])).

tff(c_421,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_42,c_413])).

tff(c_423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_380,c_421])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.31  
% 2.56/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.32  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.56/1.32  
% 2.56/1.32  %Foreground sorts:
% 2.56/1.32  
% 2.56/1.32  
% 2.56/1.32  %Background operators:
% 2.56/1.32  
% 2.56/1.32  
% 2.56/1.32  %Foreground operators:
% 2.56/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.56/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.56/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.56/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.32  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.56/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.56/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.56/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.56/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.56/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.56/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.56/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.56/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.56/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.32  
% 2.56/1.33  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 2.56/1.33  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.56/1.33  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.56/1.33  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.56/1.33  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.56/1.33  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.56/1.33  tff(f_62, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.56/1.33  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.56/1.33  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.56/1.33  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.56/1.33  tff(c_70, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.56/1.33  tff(c_79, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_70])).
% 2.56/1.33  tff(c_53, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.33  tff(c_62, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.56/1.33  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.56/1.33  tff(c_160, plain, (![A_90, B_91, C_92, D_93]: (k7_relset_1(A_90, B_91, C_92, D_93)=k9_relat_1(C_92, D_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.56/1.33  tff(c_167, plain, (![D_93]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_93)=k9_relat_1('#skF_5', D_93))), inference(resolution, [status(thm)], [c_38, c_160])).
% 2.56/1.33  tff(c_36, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.56/1.33  tff(c_169, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_36])).
% 2.56/1.33  tff(c_18, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_1'(A_8, B_9, C_10), k1_relat_1(C_10)) | ~r2_hidden(A_8, k9_relat_1(C_10, B_9)) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.33  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.56/1.33  tff(c_189, plain, (![A_96, B_97, C_98]: (r2_hidden(k4_tarski('#skF_1'(A_96, B_97, C_98), A_96), C_98) | ~r2_hidden(A_96, k9_relat_1(C_98, B_97)) | ~v1_relat_1(C_98))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.33  tff(c_22, plain, (![C_16, A_14, B_15]: (k1_funct_1(C_16, A_14)=B_15 | ~r2_hidden(k4_tarski(A_14, B_15), C_16) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.56/1.33  tff(c_245, plain, (![C_105, A_106, B_107]: (k1_funct_1(C_105, '#skF_1'(A_106, B_107, C_105))=A_106 | ~v1_funct_1(C_105) | ~r2_hidden(A_106, k9_relat_1(C_105, B_107)) | ~v1_relat_1(C_105))), inference(resolution, [status(thm)], [c_189, c_22])).
% 2.56/1.33  tff(c_253, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_169, c_245])).
% 2.56/1.33  tff(c_261, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_42, c_253])).
% 2.56/1.33  tff(c_20, plain, (![A_14, C_16]: (r2_hidden(k4_tarski(A_14, k1_funct_1(C_16, A_14)), C_16) | ~r2_hidden(A_14, k1_relat_1(C_16)) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.56/1.33  tff(c_266, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_261, c_20])).
% 2.56/1.33  tff(c_270, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_42, c_266])).
% 2.56/1.33  tff(c_288, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_270])).
% 2.56/1.33  tff(c_291, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_288])).
% 2.56/1.33  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_169, c_291])).
% 2.56/1.33  tff(c_297, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_270])).
% 2.56/1.33  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.33  tff(c_123, plain, (![A_59, C_60, B_61]: (m1_subset_1(A_59, C_60) | ~m1_subset_1(B_61, k1_zfmisc_1(C_60)) | ~r2_hidden(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.33  tff(c_128, plain, (![A_59, B_2, A_1]: (m1_subset_1(A_59, B_2) | ~r2_hidden(A_59, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_123])).
% 2.56/1.33  tff(c_342, plain, (![B_114]: (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), B_114) | ~r1_tarski(k1_relat_1('#skF_5'), B_114))), inference(resolution, [status(thm)], [c_297, c_128])).
% 2.56/1.33  tff(c_346, plain, (![A_6]: (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), A_6) | ~v4_relat_1('#skF_5', A_6) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_342])).
% 2.56/1.33  tff(c_350, plain, (![A_115]: (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), A_115) | ~v4_relat_1('#skF_5', A_115))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_346])).
% 2.56/1.33  tff(c_140, plain, (![A_79, B_80, C_81]: (r2_hidden('#skF_1'(A_79, B_80, C_81), B_80) | ~r2_hidden(A_79, k9_relat_1(C_81, B_80)) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.33  tff(c_34, plain, (![F_31]: (k1_funct_1('#skF_5', F_31)!='#skF_6' | ~r2_hidden(F_31, '#skF_4') | ~m1_subset_1(F_31, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.56/1.33  tff(c_148, plain, (![A_79, C_81]: (k1_funct_1('#skF_5', '#skF_1'(A_79, '#skF_4', C_81))!='#skF_6' | ~m1_subset_1('#skF_1'(A_79, '#skF_4', C_81), '#skF_2') | ~r2_hidden(A_79, k9_relat_1(C_81, '#skF_4')) | ~v1_relat_1(C_81))), inference(resolution, [status(thm)], [c_140, c_34])).
% 2.56/1.33  tff(c_181, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_169, c_148])).
% 2.56/1.33  tff(c_186, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_181])).
% 2.56/1.33  tff(c_220, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_186])).
% 2.56/1.33  tff(c_353, plain, (~v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_350, c_220])).
% 2.56/1.33  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_353])).
% 2.56/1.33  tff(c_380, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(splitRight, [status(thm)], [c_186])).
% 2.56/1.33  tff(c_405, plain, (![C_118, A_119, B_120]: (k1_funct_1(C_118, '#skF_1'(A_119, B_120, C_118))=A_119 | ~v1_funct_1(C_118) | ~r2_hidden(A_119, k9_relat_1(C_118, B_120)) | ~v1_relat_1(C_118))), inference(resolution, [status(thm)], [c_189, c_22])).
% 2.56/1.33  tff(c_413, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_169, c_405])).
% 2.56/1.33  tff(c_421, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_42, c_413])).
% 2.56/1.33  tff(c_423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_380, c_421])).
% 2.56/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.33  
% 2.56/1.33  Inference rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Ref     : 0
% 2.56/1.33  #Sup     : 81
% 2.56/1.33  #Fact    : 0
% 2.56/1.33  #Define  : 0
% 2.56/1.33  #Split   : 3
% 2.56/1.33  #Chain   : 0
% 2.56/1.33  #Close   : 0
% 2.56/1.33  
% 2.56/1.33  Ordering : KBO
% 2.56/1.33  
% 2.56/1.33  Simplification rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Subsume      : 3
% 2.56/1.33  #Demod        : 23
% 2.56/1.33  #Tautology    : 16
% 2.56/1.33  #SimpNegUnit  : 1
% 2.56/1.33  #BackRed      : 2
% 2.56/1.33  
% 2.56/1.33  #Partial instantiations: 0
% 2.56/1.33  #Strategies tried      : 1
% 2.56/1.33  
% 2.56/1.33  Timing (in seconds)
% 2.56/1.33  ----------------------
% 2.56/1.33  Preprocessing        : 0.31
% 2.56/1.34  Parsing              : 0.16
% 2.56/1.34  CNF conversion       : 0.02
% 2.56/1.34  Main loop            : 0.26
% 2.56/1.34  Inferencing          : 0.10
% 2.56/1.34  Reduction            : 0.07
% 2.56/1.34  Demodulation         : 0.05
% 2.56/1.34  BG Simplification    : 0.02
% 2.56/1.34  Subsumption          : 0.05
% 2.56/1.34  Abstraction          : 0.02
% 2.56/1.34  MUC search           : 0.00
% 2.56/1.34  Cooper               : 0.00
% 2.56/1.34  Total                : 0.61
% 2.56/1.34  Index Insertion      : 0.00
% 2.56/1.34  Index Deletion       : 0.00
% 2.56/1.34  Index Matching       : 0.00
% 2.56/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
