%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:26 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 117 expanded)
%              Number of leaves         :   31 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 273 expanded)
%              Number of equality atoms :   16 (  34 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_42])).

tff(c_582,plain,(
    ! [A_181,B_182,C_183] :
      ( r2_hidden(k4_tarski('#skF_1'(A_181,B_182,C_183),A_181),C_183)
      | ~ r2_hidden(A_181,k9_relat_1(C_183,B_182))
      | ~ v1_relat_1(C_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k7_relset_1(A_73,B_74,C_75,D_76) = k9_relat_1(C_75,D_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_126,plain,(
    ! [D_76] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_76) = k9_relat_1('#skF_5',D_76) ),
    inference(resolution,[status(thm)],[c_36,c_123])).

tff(c_34,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_157,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_34])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_1'(A_13,B_14,C_15),B_14)
      | ~ r2_hidden(A_13,k9_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden(k4_tarski('#skF_1'(A_13,B_14,C_15),A_13),C_15)
      | ~ r2_hidden(A_13,k9_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_47,plain,(
    ! [C_39,B_40,A_41] :
      ( ~ v1_xboole_0(C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_41,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_47])).

tff(c_51,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_58,plain,(
    ! [A_43,C_44,B_45] :
      ( m1_subset_1(A_43,C_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [A_43] :
      ( m1_subset_1(A_43,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_43,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [A_51,C_52,B_53,D_54] :
      ( r2_hidden(A_51,C_52)
      | ~ r2_hidden(k4_tarski(A_51,B_53),k2_zfmisc_1(C_52,D_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_194,plain,(
    ! [A_89,C_90,D_91,B_92] :
      ( r2_hidden(A_89,C_90)
      | v1_xboole_0(k2_zfmisc_1(C_90,D_91))
      | ~ m1_subset_1(k4_tarski(A_89,B_92),k2_zfmisc_1(C_90,D_91)) ) ),
    inference(resolution,[status(thm)],[c_8,c_68])).

tff(c_198,plain,(
    ! [A_89,B_92] :
      ( r2_hidden(A_89,'#skF_2')
      | v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(k4_tarski(A_89,B_92),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_61,c_194])).

tff(c_238,plain,(
    ! [A_96,B_97] :
      ( r2_hidden(A_96,'#skF_2')
      | ~ r2_hidden(k4_tarski(A_96,B_97),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_198])).

tff(c_242,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_13,k9_relat_1('#skF_5',B_14))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_238])).

tff(c_313,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_1'(A_101,B_102,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_101,k9_relat_1('#skF_5',B_102)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_242])).

tff(c_32,plain,(
    ! [F_33] :
      ( k1_funct_1('#skF_5',F_33) != '#skF_6'
      | ~ r2_hidden(F_33,'#skF_4')
      | ~ r2_hidden(F_33,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_371,plain,(
    ! [A_113,B_114] :
      ( k1_funct_1('#skF_5','#skF_1'(A_113,B_114,'#skF_5')) != '#skF_6'
      | ~ r2_hidden('#skF_1'(A_113,B_114,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_113,k9_relat_1('#skF_5',B_114)) ) ),
    inference(resolution,[status(thm)],[c_313,c_32])).

tff(c_375,plain,(
    ! [A_13] :
      ( k1_funct_1('#skF_5','#skF_1'(A_13,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_13,k9_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_371])).

tff(c_383,plain,(
    ! [A_115] :
      ( k1_funct_1('#skF_5','#skF_1'(A_115,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_115,k9_relat_1('#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_375])).

tff(c_404,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_157,c_383])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_202,plain,(
    ! [A_93,B_94,C_95] :
      ( r2_hidden(k4_tarski('#skF_1'(A_93,B_94,C_95),A_93),C_95)
      | ~ r2_hidden(A_93,k9_relat_1(C_95,B_94))
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_funct_1(C_21,A_19) = B_20
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_431,plain,(
    ! [C_124,A_125,B_126] :
      ( k1_funct_1(C_124,'#skF_1'(A_125,B_126,C_124)) = A_125
      | ~ v1_funct_1(C_124)
      | ~ r2_hidden(A_125,k9_relat_1(C_124,B_126))
      | ~ v1_relat_1(C_124) ) ),
    inference(resolution,[status(thm)],[c_202,c_24])).

tff(c_436,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_157,c_431])).

tff(c_449,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_436])).

tff(c_451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_449])).

tff(c_452,plain,(
    ! [A_41] : ~ r2_hidden(A_41,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_616,plain,(
    ! [A_181,B_182] :
      ( ~ r2_hidden(A_181,k9_relat_1('#skF_5',B_182))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_582,c_452])).

tff(c_627,plain,(
    ! [A_181,B_182] : ~ r2_hidden(A_181,k9_relat_1('#skF_5',B_182)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_616])).

tff(c_564,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( k7_relset_1(A_165,B_166,C_167,D_168) = k9_relat_1(C_167,D_168)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_567,plain,(
    ! [D_168] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_168) = k9_relat_1('#skF_5',D_168) ),
    inference(resolution,[status(thm)],[c_36,c_564])).

tff(c_568,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_34])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_627,c_568])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:29:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.39  
% 2.70/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.40  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.70/1.40  
% 2.70/1.40  %Foreground sorts:
% 2.70/1.40  
% 2.70/1.40  
% 2.70/1.40  %Background operators:
% 2.70/1.40  
% 2.70/1.40  
% 2.70/1.40  %Foreground operators:
% 2.70/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.70/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.70/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.70/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.70/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.70/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.70/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.70/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.40  
% 2.70/1.41  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 2.70/1.41  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.70/1.41  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.70/1.41  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.70/1.41  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.70/1.41  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.70/1.41  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.70/1.41  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.70/1.41  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.70/1.41  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.70/1.41  tff(c_42, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.70/1.41  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_42])).
% 2.70/1.41  tff(c_582, plain, (![A_181, B_182, C_183]: (r2_hidden(k4_tarski('#skF_1'(A_181, B_182, C_183), A_181), C_183) | ~r2_hidden(A_181, k9_relat_1(C_183, B_182)) | ~v1_relat_1(C_183))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.70/1.41  tff(c_123, plain, (![A_73, B_74, C_75, D_76]: (k7_relset_1(A_73, B_74, C_75, D_76)=k9_relat_1(C_75, D_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.70/1.41  tff(c_126, plain, (![D_76]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_76)=k9_relat_1('#skF_5', D_76))), inference(resolution, [status(thm)], [c_36, c_123])).
% 2.70/1.41  tff(c_34, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.70/1.41  tff(c_157, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_34])).
% 2.70/1.41  tff(c_16, plain, (![A_13, B_14, C_15]: (r2_hidden('#skF_1'(A_13, B_14, C_15), B_14) | ~r2_hidden(A_13, k9_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.70/1.41  tff(c_18, plain, (![A_13, B_14, C_15]: (r2_hidden(k4_tarski('#skF_1'(A_13, B_14, C_15), A_13), C_15) | ~r2_hidden(A_13, k9_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.70/1.41  tff(c_47, plain, (![C_39, B_40, A_41]: (~v1_xboole_0(C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.70/1.41  tff(c_50, plain, (![A_41]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_41, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_47])).
% 2.70/1.41  tff(c_51, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 2.70/1.41  tff(c_58, plain, (![A_43, C_44, B_45]: (m1_subset_1(A_43, C_44) | ~m1_subset_1(B_45, k1_zfmisc_1(C_44)) | ~r2_hidden(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.41  tff(c_61, plain, (![A_43]: (m1_subset_1(A_43, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_43, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_58])).
% 2.70/1.41  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.41  tff(c_68, plain, (![A_51, C_52, B_53, D_54]: (r2_hidden(A_51, C_52) | ~r2_hidden(k4_tarski(A_51, B_53), k2_zfmisc_1(C_52, D_54)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.41  tff(c_194, plain, (![A_89, C_90, D_91, B_92]: (r2_hidden(A_89, C_90) | v1_xboole_0(k2_zfmisc_1(C_90, D_91)) | ~m1_subset_1(k4_tarski(A_89, B_92), k2_zfmisc_1(C_90, D_91)))), inference(resolution, [status(thm)], [c_8, c_68])).
% 2.70/1.41  tff(c_198, plain, (![A_89, B_92]: (r2_hidden(A_89, '#skF_2') | v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(k4_tarski(A_89, B_92), '#skF_5'))), inference(resolution, [status(thm)], [c_61, c_194])).
% 2.70/1.41  tff(c_238, plain, (![A_96, B_97]: (r2_hidden(A_96, '#skF_2') | ~r2_hidden(k4_tarski(A_96, B_97), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_51, c_198])).
% 2.70/1.41  tff(c_242, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14, '#skF_5'), '#skF_2') | ~r2_hidden(A_13, k9_relat_1('#skF_5', B_14)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_18, c_238])).
% 2.70/1.41  tff(c_313, plain, (![A_101, B_102]: (r2_hidden('#skF_1'(A_101, B_102, '#skF_5'), '#skF_2') | ~r2_hidden(A_101, k9_relat_1('#skF_5', B_102)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_242])).
% 2.70/1.41  tff(c_32, plain, (![F_33]: (k1_funct_1('#skF_5', F_33)!='#skF_6' | ~r2_hidden(F_33, '#skF_4') | ~r2_hidden(F_33, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.70/1.41  tff(c_371, plain, (![A_113, B_114]: (k1_funct_1('#skF_5', '#skF_1'(A_113, B_114, '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'(A_113, B_114, '#skF_5'), '#skF_4') | ~r2_hidden(A_113, k9_relat_1('#skF_5', B_114)))), inference(resolution, [status(thm)], [c_313, c_32])).
% 2.70/1.41  tff(c_375, plain, (![A_13]: (k1_funct_1('#skF_5', '#skF_1'(A_13, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_13, k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_371])).
% 2.70/1.41  tff(c_383, plain, (![A_115]: (k1_funct_1('#skF_5', '#skF_1'(A_115, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_115, k9_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_375])).
% 2.70/1.41  tff(c_404, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(resolution, [status(thm)], [c_157, c_383])).
% 2.70/1.41  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.70/1.41  tff(c_202, plain, (![A_93, B_94, C_95]: (r2_hidden(k4_tarski('#skF_1'(A_93, B_94, C_95), A_93), C_95) | ~r2_hidden(A_93, k9_relat_1(C_95, B_94)) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.70/1.41  tff(c_24, plain, (![C_21, A_19, B_20]: (k1_funct_1(C_21, A_19)=B_20 | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.41  tff(c_431, plain, (![C_124, A_125, B_126]: (k1_funct_1(C_124, '#skF_1'(A_125, B_126, C_124))=A_125 | ~v1_funct_1(C_124) | ~r2_hidden(A_125, k9_relat_1(C_124, B_126)) | ~v1_relat_1(C_124))), inference(resolution, [status(thm)], [c_202, c_24])).
% 2.70/1.41  tff(c_436, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_157, c_431])).
% 2.70/1.41  tff(c_449, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_436])).
% 2.70/1.41  tff(c_451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_404, c_449])).
% 2.70/1.41  tff(c_452, plain, (![A_41]: (~r2_hidden(A_41, '#skF_5'))), inference(splitRight, [status(thm)], [c_50])).
% 2.70/1.41  tff(c_616, plain, (![A_181, B_182]: (~r2_hidden(A_181, k9_relat_1('#skF_5', B_182)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_582, c_452])).
% 2.70/1.41  tff(c_627, plain, (![A_181, B_182]: (~r2_hidden(A_181, k9_relat_1('#skF_5', B_182)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_616])).
% 2.70/1.41  tff(c_564, plain, (![A_165, B_166, C_167, D_168]: (k7_relset_1(A_165, B_166, C_167, D_168)=k9_relat_1(C_167, D_168) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.70/1.41  tff(c_567, plain, (![D_168]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_168)=k9_relat_1('#skF_5', D_168))), inference(resolution, [status(thm)], [c_36, c_564])).
% 2.70/1.41  tff(c_568, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_567, c_34])).
% 2.70/1.41  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_627, c_568])).
% 2.70/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.41  
% 2.70/1.41  Inference rules
% 2.70/1.41  ----------------------
% 2.70/1.41  #Ref     : 0
% 2.70/1.41  #Sup     : 112
% 2.70/1.41  #Fact    : 0
% 2.70/1.41  #Define  : 0
% 2.70/1.41  #Split   : 10
% 2.70/1.41  #Chain   : 0
% 2.70/1.41  #Close   : 0
% 2.70/1.41  
% 2.70/1.41  Ordering : KBO
% 2.70/1.41  
% 2.70/1.41  Simplification rules
% 2.70/1.41  ----------------------
% 2.70/1.41  #Subsume      : 4
% 2.70/1.41  #Demod        : 14
% 2.70/1.41  #Tautology    : 11
% 2.70/1.41  #SimpNegUnit  : 6
% 2.70/1.41  #BackRed      : 3
% 2.70/1.41  
% 2.70/1.41  #Partial instantiations: 0
% 2.70/1.41  #Strategies tried      : 1
% 2.70/1.41  
% 2.70/1.41  Timing (in seconds)
% 2.70/1.41  ----------------------
% 2.70/1.41  Preprocessing        : 0.32
% 2.70/1.41  Parsing              : 0.17
% 2.70/1.41  CNF conversion       : 0.02
% 2.70/1.41  Main loop            : 0.32
% 2.70/1.41  Inferencing          : 0.13
% 2.70/1.41  Reduction            : 0.08
% 2.70/1.41  Demodulation         : 0.06
% 2.70/1.41  BG Simplification    : 0.02
% 2.70/1.41  Subsumption          : 0.07
% 2.70/1.41  Abstraction          : 0.02
% 2.70/1.41  MUC search           : 0.00
% 2.70/1.42  Cooper               : 0.00
% 2.70/1.42  Total                : 0.67
% 2.70/1.42  Index Insertion      : 0.00
% 2.70/1.42  Index Deletion       : 0.00
% 2.70/1.42  Index Matching       : 0.00
% 2.70/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
