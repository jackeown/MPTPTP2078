%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1016+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:15 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 186 expanded)
%              Number of leaves         :   25 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 ( 598 expanded)
%              Number of equality atoms :   45 ( 156 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_44])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_49,plain,(
    ! [A_25] :
      ( '#skF_2'(A_25) != '#skF_1'(A_25)
      | v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_43,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_52,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_49,c_43])).

tff(c_55,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22,c_52])).

tff(c_20,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_58,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_58])).

tff(c_95,plain,(
    ! [A_34,B_35] :
      ( k1_relset_1(A_34,A_34,B_35) = A_34
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_zfmisc_1(A_34,A_34)))
      | ~ v1_funct_2(B_35,A_34,A_34)
      | ~ v1_funct_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_98,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_95])).

tff(c_101,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_62,c_98])).

tff(c_12,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),k1_relat_1(A_4))
      | v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_106,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_12])).

tff(c_113,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22,c_106])).

tff(c_114,plain,(
    r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_113])).

tff(c_10,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_2'(A_4),k1_relat_1(A_4))
      | v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_109,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_10])).

tff(c_116,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22,c_109])).

tff(c_117,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_116])).

tff(c_8,plain,(
    ! [A_4] :
      ( k1_funct_1(A_4,'#skF_2'(A_4)) = k1_funct_1(A_4,'#skF_1'(A_4))
      | v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    ! [D_21,C_20] :
      ( v2_funct_1('#skF_4')
      | D_21 = C_20
      | k1_funct_1('#skF_4',D_21) != k1_funct_1('#skF_4',C_20)
      | ~ r2_hidden(D_21,'#skF_3')
      | ~ r2_hidden(C_20,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_82,plain,(
    ! [D_32,C_33] :
      ( D_32 = C_33
      | k1_funct_1('#skF_4',D_32) != k1_funct_1('#skF_4',C_33)
      | ~ r2_hidden(D_32,'#skF_3')
      | ~ r2_hidden(C_33,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_42])).

tff(c_88,plain,(
    ! [D_32] :
      ( D_32 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_32) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_32,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_82])).

tff(c_93,plain,(
    ! [D_32] :
      ( D_32 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_32) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_32,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22,c_88])).

tff(c_94,plain,(
    ! [D_32] :
      ( D_32 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_32) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_32,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_93])).

tff(c_124,plain,(
    ! [D_32] :
      ( D_32 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_32) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_32,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_94])).

tff(c_127,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_124])).

tff(c_129,plain,(
    '#skF_2'('#skF_4') = '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_127])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_129])).

tff(c_132,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_133,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_135,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_28])).

tff(c_138,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_142,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_138])).

tff(c_153,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_157,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_153])).

tff(c_173,plain,(
    ! [A_46,B_47] :
      ( k1_relset_1(A_46,A_46,B_47) = A_46
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k2_zfmisc_1(A_46,A_46)))
      | ~ v1_funct_2(B_47,A_46,A_46)
      | ~ v1_funct_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_176,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_173])).

tff(c_179,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_157,c_176])).

tff(c_30,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_137,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_30])).

tff(c_26,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_144,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_26])).

tff(c_204,plain,(
    ! [C_48,B_49,A_50] :
      ( C_48 = B_49
      | k1_funct_1(A_50,C_48) != k1_funct_1(A_50,B_49)
      | ~ r2_hidden(C_48,k1_relat_1(A_50))
      | ~ r2_hidden(B_49,k1_relat_1(A_50))
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_210,plain,(
    ! [B_49] :
      ( B_49 = '#skF_5'
      | k1_funct_1('#skF_4',B_49) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_49,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_204])).

tff(c_217,plain,(
    ! [B_51] :
      ( B_51 = '#skF_5'
      | k1_funct_1('#skF_4',B_51) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_51,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_22,c_133,c_179,c_137,c_179,c_210])).

tff(c_223,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_135,c_217])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_223])).

%------------------------------------------------------------------------------
