%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:44 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 201 expanded)
%              Number of leaves         :   26 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  162 ( 628 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_79,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_49,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_47,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_47])).

tff(c_53,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_50])).

tff(c_24,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_54,plain,(
    ! [A_28] :
      ( '#skF_2'(A_28) != '#skF_1'(A_28)
      | v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_45,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_57,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_45])).

tff(c_60,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_24,c_57])).

tff(c_22,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_63,plain,(
    ! [A_31,B_32,C_33] :
      ( k1_relset_1(A_31,B_32,C_33) = k1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_63])).

tff(c_100,plain,(
    ! [A_37,B_38] :
      ( k1_relset_1(A_37,A_37,B_38) = A_37
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k2_zfmisc_1(A_37,A_37)))
      | ~ v1_funct_2(B_38,A_37,A_37)
      | ~ v1_funct_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_103,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_100])).

tff(c_106,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_67,c_103])).

tff(c_14,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),k1_relat_1(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_111,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_14])).

tff(c_118,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_24,c_111])).

tff(c_119,plain,(
    r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_118])).

tff(c_12,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),k1_relat_1(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_114,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_12])).

tff(c_121,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_24,c_114])).

tff(c_122,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_121])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_funct_1(A_6,'#skF_2'(A_6)) = k1_funct_1(A_6,'#skF_1'(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,(
    ! [D_23,C_22] :
      ( v2_funct_1('#skF_4')
      | D_23 = C_22
      | k1_funct_1('#skF_4',D_23) != k1_funct_1('#skF_4',C_22)
      | ~ r2_hidden(D_23,'#skF_3')
      | ~ r2_hidden(C_22,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_87,plain,(
    ! [D_35,C_36] :
      ( D_35 = C_36
      | k1_funct_1('#skF_4',D_35) != k1_funct_1('#skF_4',C_36)
      | ~ r2_hidden(D_35,'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_44])).

tff(c_93,plain,(
    ! [D_35] :
      ( D_35 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_35) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_35,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_87])).

tff(c_98,plain,(
    ! [D_35] :
      ( D_35 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_35) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_35,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_24,c_93])).

tff(c_99,plain,(
    ! [D_35] :
      ( D_35 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_35) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_35,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_98])).

tff(c_129,plain,(
    ! [D_35] :
      ( D_35 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_35) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_35,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_99])).

tff(c_132,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_129])).

tff(c_134,plain,(
    '#skF_2'('#skF_4') = '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_132])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_134])).

tff(c_137,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_138,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_30,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_141,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_30])).

tff(c_150,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_153,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_150])).

tff(c_156,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_153])).

tff(c_161,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_165,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_161])).

tff(c_179,plain,(
    ! [A_50,B_51] :
      ( k1_relset_1(A_50,A_50,B_51) = A_50
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_zfmisc_1(A_50,A_50)))
      | ~ v1_funct_2(B_51,A_50,A_50)
      | ~ v1_funct_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_182,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_179])).

tff(c_185,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_165,c_182])).

tff(c_32,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_143,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_32])).

tff(c_28,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_145,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_28])).

tff(c_212,plain,(
    ! [C_52,B_53,A_54] :
      ( C_52 = B_53
      | k1_funct_1(A_54,C_52) != k1_funct_1(A_54,B_53)
      | ~ r2_hidden(C_52,k1_relat_1(A_54))
      | ~ r2_hidden(B_53,k1_relat_1(A_54))
      | ~ v2_funct_1(A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_218,plain,(
    ! [B_53] :
      ( B_53 = '#skF_5'
      | k1_funct_1('#skF_4',B_53) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_53,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_212])).

tff(c_225,plain,(
    ! [B_55] :
      ( B_55 = '#skF_5'
      | k1_funct_1('#skF_4',B_55) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_55,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_24,c_138,c_185,c_143,c_185,c_218])).

tff(c_231,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_141,c_225])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.27  
% 2.12/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.12/1.28  
% 2.12/1.28  %Foreground sorts:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Background operators:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Foreground operators:
% 2.12/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.12/1.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.12/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.12/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.12/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.12/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.28  
% 2.12/1.29  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.12/1.29  tff(f_79, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 2.12/1.29  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.12/1.29  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 2.12/1.29  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.12/1.29  tff(f_61, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 2.12/1.29  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.12/1.29  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.29  tff(c_47, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.29  tff(c_50, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_47])).
% 2.12/1.29  tff(c_53, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_50])).
% 2.12/1.29  tff(c_24, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.29  tff(c_54, plain, (![A_28]: ('#skF_2'(A_28)!='#skF_1'(A_28) | v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.29  tff(c_26, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.29  tff(c_45, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 2.12/1.29  tff(c_57, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_45])).
% 2.12/1.29  tff(c_60, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_24, c_57])).
% 2.12/1.29  tff(c_22, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.29  tff(c_63, plain, (![A_31, B_32, C_33]: (k1_relset_1(A_31, B_32, C_33)=k1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.12/1.29  tff(c_67, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_63])).
% 2.12/1.29  tff(c_100, plain, (![A_37, B_38]: (k1_relset_1(A_37, A_37, B_38)=A_37 | ~m1_subset_1(B_38, k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))) | ~v1_funct_2(B_38, A_37, A_37) | ~v1_funct_1(B_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.29  tff(c_103, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_100])).
% 2.12/1.29  tff(c_106, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_67, c_103])).
% 2.12/1.29  tff(c_14, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), k1_relat_1(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.29  tff(c_111, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_106, c_14])).
% 2.12/1.29  tff(c_118, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_24, c_111])).
% 2.12/1.29  tff(c_119, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_45, c_118])).
% 2.12/1.29  tff(c_12, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), k1_relat_1(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.29  tff(c_114, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_106, c_12])).
% 2.12/1.29  tff(c_121, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_24, c_114])).
% 2.12/1.29  tff(c_122, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_45, c_121])).
% 2.12/1.29  tff(c_10, plain, (![A_6]: (k1_funct_1(A_6, '#skF_2'(A_6))=k1_funct_1(A_6, '#skF_1'(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.29  tff(c_44, plain, (![D_23, C_22]: (v2_funct_1('#skF_4') | D_23=C_22 | k1_funct_1('#skF_4', D_23)!=k1_funct_1('#skF_4', C_22) | ~r2_hidden(D_23, '#skF_3') | ~r2_hidden(C_22, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.29  tff(c_87, plain, (![D_35, C_36]: (D_35=C_36 | k1_funct_1('#skF_4', D_35)!=k1_funct_1('#skF_4', C_36) | ~r2_hidden(D_35, '#skF_3') | ~r2_hidden(C_36, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_45, c_44])).
% 2.12/1.29  tff(c_93, plain, (![D_35]: (D_35='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_35)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_35, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_87])).
% 2.12/1.29  tff(c_98, plain, (![D_35]: (D_35='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_35)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_35, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_24, c_93])).
% 2.12/1.29  tff(c_99, plain, (![D_35]: (D_35='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_35)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_35, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_45, c_98])).
% 2.12/1.29  tff(c_129, plain, (![D_35]: (D_35='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_35)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_35, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_99])).
% 2.12/1.29  tff(c_132, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_129])).
% 2.12/1.29  tff(c_134, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_132])).
% 2.12/1.29  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_134])).
% 2.12/1.29  tff(c_137, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_26])).
% 2.12/1.29  tff(c_138, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 2.12/1.29  tff(c_30, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.29  tff(c_141, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_30])).
% 2.12/1.29  tff(c_150, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.29  tff(c_153, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_150])).
% 2.12/1.29  tff(c_156, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_153])).
% 2.12/1.29  tff(c_161, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.12/1.29  tff(c_165, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_161])).
% 2.12/1.29  tff(c_179, plain, (![A_50, B_51]: (k1_relset_1(A_50, A_50, B_51)=A_50 | ~m1_subset_1(B_51, k1_zfmisc_1(k2_zfmisc_1(A_50, A_50))) | ~v1_funct_2(B_51, A_50, A_50) | ~v1_funct_1(B_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.29  tff(c_182, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_179])).
% 2.12/1.29  tff(c_185, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_165, c_182])).
% 2.12/1.29  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.29  tff(c_143, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_32])).
% 2.12/1.29  tff(c_28, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.29  tff(c_145, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_28])).
% 2.12/1.29  tff(c_212, plain, (![C_52, B_53, A_54]: (C_52=B_53 | k1_funct_1(A_54, C_52)!=k1_funct_1(A_54, B_53) | ~r2_hidden(C_52, k1_relat_1(A_54)) | ~r2_hidden(B_53, k1_relat_1(A_54)) | ~v2_funct_1(A_54) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.29  tff(c_218, plain, (![B_53]: (B_53='#skF_5' | k1_funct_1('#skF_4', B_53)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_53, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_212])).
% 2.12/1.29  tff(c_225, plain, (![B_55]: (B_55='#skF_5' | k1_funct_1('#skF_4', B_55)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(B_55, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_24, c_138, c_185, c_143, c_185, c_218])).
% 2.12/1.29  tff(c_231, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_141, c_225])).
% 2.12/1.29  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_231])).
% 2.12/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  Inference rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Ref     : 3
% 2.12/1.29  #Sup     : 37
% 2.12/1.29  #Fact    : 0
% 2.12/1.29  #Define  : 0
% 2.12/1.29  #Split   : 2
% 2.12/1.29  #Chain   : 0
% 2.12/1.29  #Close   : 0
% 2.12/1.29  
% 2.12/1.29  Ordering : KBO
% 2.12/1.29  
% 2.12/1.29  Simplification rules
% 2.12/1.29  ----------------------
% 2.12/1.30  #Subsume      : 6
% 2.12/1.30  #Demod        : 48
% 2.12/1.30  #Tautology    : 30
% 2.12/1.30  #SimpNegUnit  : 7
% 2.12/1.30  #BackRed      : 2
% 2.12/1.30  
% 2.12/1.30  #Partial instantiations: 0
% 2.12/1.30  #Strategies tried      : 1
% 2.12/1.30  
% 2.12/1.30  Timing (in seconds)
% 2.12/1.30  ----------------------
% 2.12/1.30  Preprocessing        : 0.32
% 2.12/1.30  Parsing              : 0.16
% 2.12/1.30  CNF conversion       : 0.02
% 2.12/1.30  Main loop            : 0.21
% 2.12/1.30  Inferencing          : 0.08
% 2.12/1.30  Reduction            : 0.06
% 2.12/1.30  Demodulation         : 0.04
% 2.12/1.30  BG Simplification    : 0.02
% 2.12/1.30  Subsumption          : 0.03
% 2.12/1.30  Abstraction          : 0.01
% 2.12/1.30  MUC search           : 0.00
% 2.12/1.30  Cooper               : 0.00
% 2.12/1.30  Total                : 0.56
% 2.12/1.30  Index Insertion      : 0.00
% 2.12/1.30  Index Deletion       : 0.00
% 2.12/1.30  Index Matching       : 0.00
% 2.12/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
