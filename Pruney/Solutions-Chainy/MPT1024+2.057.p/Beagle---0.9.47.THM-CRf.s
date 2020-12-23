%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:29 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 189 expanded)
%              Number of leaves         :   34 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 ( 469 expanded)
%              Number of equality atoms :   15 (  63 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_120,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_129,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_120])).

tff(c_164,plain,(
    ! [A_74,B_75,C_76] :
      ( m1_subset_1(k1_relset_1(A_74,B_75,C_76),k1_zfmisc_1(A_74))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_180,plain,
    ( m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_164])).

tff(c_185,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_180])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_194,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_8])).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_70])).

tff(c_80,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_76])).

tff(c_306,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k7_relset_1(A_105,B_106,C_107,D_108) = k9_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_317,plain,(
    ! [D_108] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_108) = k9_relat_1('#skF_6',D_108) ),
    inference(resolution,[status(thm)],[c_40,c_306])).

tff(c_38,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_319,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_38])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_400,plain,(
    ! [A_126,B_127,C_128] :
      ( r2_hidden(k4_tarski('#skF_2'(A_126,B_127,C_128),A_126),C_128)
      | ~ r2_hidden(A_126,k9_relat_1(C_128,B_127))
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_funct_1(C_21,A_19) = B_20
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_774,plain,(
    ! [C_174,A_175,B_176] :
      ( k1_funct_1(C_174,'#skF_2'(A_175,B_176,C_174)) = A_175
      | ~ v1_funct_1(C_174)
      | ~ r2_hidden(A_175,k9_relat_1(C_174,B_176))
      | ~ v1_relat_1(C_174) ) ),
    inference(resolution,[status(thm)],[c_400,c_26])).

tff(c_785,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_319,c_774])).

tff(c_800,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_44,c_785])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_2'(A_13,B_14,C_15),k1_relat_1(C_15))
      | ~ r2_hidden(A_13,k9_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    ! [A_19,C_21] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1(C_21,A_19)),C_21)
      | ~ r2_hidden(A_19,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_807,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_24])).

tff(c_811,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_44,c_807])).

tff(c_813,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_811])).

tff(c_816,plain,
    ( ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_813])).

tff(c_820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_319,c_816])).

tff(c_822,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_811])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_848,plain,(
    ! [B_179] :
      ( r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),B_179)
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_179) ) ),
    inference(resolution,[status(thm)],[c_822,c_2])).

tff(c_155,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden('#skF_2'(A_71,B_72,C_73),B_72)
      | ~ r2_hidden(A_71,k9_relat_1(C_73,B_72))
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ! [F_36] :
      ( k1_funct_1('#skF_6',F_36) != '#skF_7'
      | ~ r2_hidden(F_36,'#skF_5')
      | ~ r2_hidden(F_36,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_163,plain,(
    ! [A_71,C_73] :
      ( k1_funct_1('#skF_6','#skF_2'(A_71,'#skF_5',C_73)) != '#skF_7'
      | ~ r2_hidden('#skF_2'(A_71,'#skF_5',C_73),'#skF_3')
      | ~ r2_hidden(A_71,k9_relat_1(C_73,'#skF_5'))
      | ~ v1_relat_1(C_73) ) ),
    inference(resolution,[status(thm)],[c_155,c_36])).

tff(c_857,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_848,c_163])).

tff(c_869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_80,c_319,c_800,c_857])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.55  
% 3.16/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.55  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.16/1.55  
% 3.16/1.55  %Foreground sorts:
% 3.16/1.55  
% 3.16/1.55  
% 3.16/1.55  %Background operators:
% 3.16/1.55  
% 3.16/1.55  
% 3.16/1.55  %Foreground operators:
% 3.16/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.16/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.55  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.16/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.16/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.16/1.55  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.16/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.16/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.16/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.16/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.55  
% 3.16/1.57  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 3.16/1.57  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.16/1.57  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.16/1.57  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.16/1.57  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.16/1.57  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.16/1.57  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.16/1.57  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.16/1.57  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.16/1.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.16/1.57  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.16/1.57  tff(c_120, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.16/1.57  tff(c_129, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_120])).
% 3.16/1.57  tff(c_164, plain, (![A_74, B_75, C_76]: (m1_subset_1(k1_relset_1(A_74, B_75, C_76), k1_zfmisc_1(A_74)) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.16/1.57  tff(c_180, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_129, c_164])).
% 3.16/1.57  tff(c_185, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_180])).
% 3.16/1.57  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.16/1.57  tff(c_194, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_185, c_8])).
% 3.16/1.57  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/1.57  tff(c_70, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.57  tff(c_76, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_70])).
% 3.16/1.57  tff(c_80, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_76])).
% 3.16/1.57  tff(c_306, plain, (![A_105, B_106, C_107, D_108]: (k7_relset_1(A_105, B_106, C_107, D_108)=k9_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.16/1.57  tff(c_317, plain, (![D_108]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_108)=k9_relat_1('#skF_6', D_108))), inference(resolution, [status(thm)], [c_40, c_306])).
% 3.16/1.57  tff(c_38, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.16/1.57  tff(c_319, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_38])).
% 3.16/1.57  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.16/1.57  tff(c_400, plain, (![A_126, B_127, C_128]: (r2_hidden(k4_tarski('#skF_2'(A_126, B_127, C_128), A_126), C_128) | ~r2_hidden(A_126, k9_relat_1(C_128, B_127)) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.16/1.57  tff(c_26, plain, (![C_21, A_19, B_20]: (k1_funct_1(C_21, A_19)=B_20 | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.16/1.57  tff(c_774, plain, (![C_174, A_175, B_176]: (k1_funct_1(C_174, '#skF_2'(A_175, B_176, C_174))=A_175 | ~v1_funct_1(C_174) | ~r2_hidden(A_175, k9_relat_1(C_174, B_176)) | ~v1_relat_1(C_174))), inference(resolution, [status(thm)], [c_400, c_26])).
% 3.16/1.57  tff(c_785, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_319, c_774])).
% 3.16/1.57  tff(c_800, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_44, c_785])).
% 3.16/1.57  tff(c_22, plain, (![A_13, B_14, C_15]: (r2_hidden('#skF_2'(A_13, B_14, C_15), k1_relat_1(C_15)) | ~r2_hidden(A_13, k9_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.16/1.57  tff(c_24, plain, (![A_19, C_21]: (r2_hidden(k4_tarski(A_19, k1_funct_1(C_21, A_19)), C_21) | ~r2_hidden(A_19, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.16/1.57  tff(c_807, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_800, c_24])).
% 3.16/1.57  tff(c_811, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_44, c_807])).
% 3.16/1.57  tff(c_813, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_811])).
% 3.16/1.57  tff(c_816, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_813])).
% 3.16/1.57  tff(c_820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_319, c_816])).
% 3.16/1.57  tff(c_822, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_811])).
% 3.16/1.57  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.57  tff(c_848, plain, (![B_179]: (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), B_179) | ~r1_tarski(k1_relat_1('#skF_6'), B_179))), inference(resolution, [status(thm)], [c_822, c_2])).
% 3.16/1.57  tff(c_155, plain, (![A_71, B_72, C_73]: (r2_hidden('#skF_2'(A_71, B_72, C_73), B_72) | ~r2_hidden(A_71, k9_relat_1(C_73, B_72)) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.16/1.57  tff(c_36, plain, (![F_36]: (k1_funct_1('#skF_6', F_36)!='#skF_7' | ~r2_hidden(F_36, '#skF_5') | ~r2_hidden(F_36, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.16/1.57  tff(c_163, plain, (![A_71, C_73]: (k1_funct_1('#skF_6', '#skF_2'(A_71, '#skF_5', C_73))!='#skF_7' | ~r2_hidden('#skF_2'(A_71, '#skF_5', C_73), '#skF_3') | ~r2_hidden(A_71, k9_relat_1(C_73, '#skF_5')) | ~v1_relat_1(C_73))), inference(resolution, [status(thm)], [c_155, c_36])).
% 3.16/1.57  tff(c_857, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6') | ~r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_848, c_163])).
% 3.16/1.57  tff(c_869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_80, c_319, c_800, c_857])).
% 3.16/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.57  
% 3.16/1.57  Inference rules
% 3.16/1.57  ----------------------
% 3.16/1.57  #Ref     : 0
% 3.16/1.57  #Sup     : 177
% 3.16/1.57  #Fact    : 0
% 3.16/1.57  #Define  : 0
% 3.16/1.57  #Split   : 7
% 3.16/1.57  #Chain   : 0
% 3.16/1.57  #Close   : 0
% 3.16/1.57  
% 3.16/1.57  Ordering : KBO
% 3.16/1.57  
% 3.16/1.57  Simplification rules
% 3.16/1.57  ----------------------
% 3.16/1.57  #Subsume      : 16
% 3.16/1.57  #Demod        : 48
% 3.16/1.57  #Tautology    : 38
% 3.16/1.57  #SimpNegUnit  : 0
% 3.16/1.57  #BackRed      : 2
% 3.16/1.57  
% 3.16/1.57  #Partial instantiations: 0
% 3.16/1.57  #Strategies tried      : 1
% 3.16/1.57  
% 3.16/1.57  Timing (in seconds)
% 3.16/1.57  ----------------------
% 3.16/1.57  Preprocessing        : 0.36
% 3.16/1.57  Parsing              : 0.18
% 3.16/1.57  CNF conversion       : 0.03
% 3.16/1.57  Main loop            : 0.39
% 3.16/1.57  Inferencing          : 0.15
% 3.16/1.57  Reduction            : 0.11
% 3.16/1.57  Demodulation         : 0.08
% 3.16/1.57  BG Simplification    : 0.02
% 3.16/1.57  Subsumption          : 0.08
% 3.16/1.57  Abstraction          : 0.02
% 3.16/1.57  MUC search           : 0.00
% 3.16/1.57  Cooper               : 0.00
% 3.16/1.57  Total                : 0.78
% 3.16/1.57  Index Insertion      : 0.00
% 3.16/1.57  Index Deletion       : 0.00
% 3.16/1.57  Index Matching       : 0.00
% 3.16/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
