%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:43 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.09s
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

tff(f_74,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
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

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_44])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_49,plain,(
    ! [A_25] :
      ( '#skF_2'(A_25) != '#skF_1'(A_25)
      | v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

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
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_58,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_58])).

tff(c_94,plain,(
    ! [A_34,B_35] :
      ( k1_relset_1(A_34,A_34,B_35) = A_34
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_zfmisc_1(A_34,A_34)))
      | ~ v1_funct_2(B_35,A_34,A_34)
      | ~ v1_funct_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_94])).

tff(c_100,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_62,c_97])).

tff(c_10,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_108,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_10])).

tff(c_115,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22,c_108])).

tff(c_116,plain,(
    r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_115])).

tff(c_8,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_105,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_8])).

tff(c_112,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22,c_105])).

tff(c_113,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_112])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_funct_1(A_1,'#skF_2'(A_1)) = k1_funct_1(A_1,'#skF_1'(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,(
    ! [D_21,C_20] :
      ( v2_funct_1('#skF_4')
      | D_21 = C_20
      | k1_funct_1('#skF_4',D_21) != k1_funct_1('#skF_4',C_20)
      | ~ r2_hidden(D_21,'#skF_3')
      | ~ r2_hidden(C_20,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_81,plain,(
    ! [D_32,C_33] :
      ( D_32 = C_33
      | k1_funct_1('#skF_4',D_32) != k1_funct_1('#skF_4',C_33)
      | ~ r2_hidden(D_32,'#skF_3')
      | ~ r2_hidden(C_33,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_42])).

tff(c_84,plain,(
    ! [C_33] :
      ( C_33 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_33) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_33,'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_81])).

tff(c_89,plain,(
    ! [C_33] :
      ( C_33 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_33) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_33,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22,c_84])).

tff(c_90,plain,(
    ! [C_33] :
      ( C_33 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_33) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_33,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_89])).

tff(c_123,plain,(
    ! [C_33] :
      ( C_33 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_33) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(C_33,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_90])).

tff(c_126,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_123])).

tff(c_128,plain,(
    '#skF_2'('#skF_4') = '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_126])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_128])).

tff(c_131,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_132,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_134,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_28])).

tff(c_137,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_141,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_137])).

tff(c_151,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_155,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_151])).

tff(c_172,plain,(
    ! [A_46,B_47] :
      ( k1_relset_1(A_46,A_46,B_47) = A_46
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k2_zfmisc_1(A_46,A_46)))
      | ~ v1_funct_2(B_47,A_46,A_46)
      | ~ v1_funct_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_175,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_172])).

tff(c_178,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_155,c_175])).

tff(c_30,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_136,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_30])).

tff(c_26,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_143,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_26])).

tff(c_203,plain,(
    ! [C_48,B_49,A_50] :
      ( C_48 = B_49
      | k1_funct_1(A_50,C_48) != k1_funct_1(A_50,B_49)
      | ~ r2_hidden(C_48,k1_relat_1(A_50))
      | ~ r2_hidden(B_49,k1_relat_1(A_50))
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_209,plain,(
    ! [B_49] :
      ( B_49 = '#skF_5'
      | k1_funct_1('#skF_4',B_49) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_49,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_203])).

tff(c_216,plain,(
    ! [B_51] :
      ( B_51 = '#skF_5'
      | k1_funct_1('#skF_4',B_51) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_51,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_22,c_132,c_178,c_136,c_178,c_209])).

tff(c_222,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_134,c_216])).

tff(c_230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.21  
% 2.09/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.21  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.09/1.21  
% 2.09/1.21  %Foreground sorts:
% 2.09/1.21  
% 2.09/1.21  
% 2.09/1.21  %Background operators:
% 2.09/1.21  
% 2.09/1.21  
% 2.09/1.21  %Foreground operators:
% 2.09/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.09/1.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.09/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.09/1.21  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.09/1.21  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.09/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.09/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.22  
% 2.09/1.23  tff(f_74, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 2.09/1.23  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.09/1.23  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 2.09/1.23  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.09/1.23  tff(f_56, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 2.09/1.23  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.23  tff(c_44, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.09/1.23  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_44])).
% 2.09/1.23  tff(c_22, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.23  tff(c_49, plain, (![A_25]: ('#skF_2'(A_25)!='#skF_1'(A_25) | v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.23  tff(c_24, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.23  tff(c_43, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 2.09/1.23  tff(c_52, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_49, c_43])).
% 2.09/1.23  tff(c_55, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22, c_52])).
% 2.09/1.23  tff(c_20, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.23  tff(c_58, plain, (![A_28, B_29, C_30]: (k1_relset_1(A_28, B_29, C_30)=k1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.23  tff(c_62, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_58])).
% 2.09/1.23  tff(c_94, plain, (![A_34, B_35]: (k1_relset_1(A_34, A_34, B_35)=A_34 | ~m1_subset_1(B_35, k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))) | ~v1_funct_2(B_35, A_34, A_34) | ~v1_funct_1(B_35))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.23  tff(c_97, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_94])).
% 2.09/1.23  tff(c_100, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_62, c_97])).
% 2.09/1.23  tff(c_10, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), k1_relat_1(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.23  tff(c_108, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_100, c_10])).
% 2.09/1.23  tff(c_115, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22, c_108])).
% 2.09/1.23  tff(c_116, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_43, c_115])).
% 2.09/1.23  tff(c_8, plain, (![A_1]: (r2_hidden('#skF_2'(A_1), k1_relat_1(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.23  tff(c_105, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_100, c_8])).
% 2.09/1.23  tff(c_112, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22, c_105])).
% 2.09/1.23  tff(c_113, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_43, c_112])).
% 2.09/1.23  tff(c_6, plain, (![A_1]: (k1_funct_1(A_1, '#skF_2'(A_1))=k1_funct_1(A_1, '#skF_1'(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.23  tff(c_42, plain, (![D_21, C_20]: (v2_funct_1('#skF_4') | D_21=C_20 | k1_funct_1('#skF_4', D_21)!=k1_funct_1('#skF_4', C_20) | ~r2_hidden(D_21, '#skF_3') | ~r2_hidden(C_20, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.23  tff(c_81, plain, (![D_32, C_33]: (D_32=C_33 | k1_funct_1('#skF_4', D_32)!=k1_funct_1('#skF_4', C_33) | ~r2_hidden(D_32, '#skF_3') | ~r2_hidden(C_33, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_43, c_42])).
% 2.09/1.23  tff(c_84, plain, (![C_33]: (C_33='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_33)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_33, '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_81])).
% 2.09/1.23  tff(c_89, plain, (![C_33]: (C_33='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_33)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_33, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22, c_84])).
% 2.09/1.23  tff(c_90, plain, (![C_33]: (C_33='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_33)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_33, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_43, c_89])).
% 2.09/1.23  tff(c_123, plain, (![C_33]: (C_33='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_33)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(C_33, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_90])).
% 2.09/1.23  tff(c_126, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_123])).
% 2.09/1.23  tff(c_128, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_126])).
% 2.09/1.23  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_128])).
% 2.09/1.23  tff(c_131, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_24])).
% 2.09/1.23  tff(c_132, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_24])).
% 2.09/1.23  tff(c_28, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.23  tff(c_134, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_28])).
% 2.09/1.23  tff(c_137, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.09/1.23  tff(c_141, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_137])).
% 2.09/1.23  tff(c_151, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.23  tff(c_155, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_151])).
% 2.09/1.23  tff(c_172, plain, (![A_46, B_47]: (k1_relset_1(A_46, A_46, B_47)=A_46 | ~m1_subset_1(B_47, k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))) | ~v1_funct_2(B_47, A_46, A_46) | ~v1_funct_1(B_47))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.23  tff(c_175, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_172])).
% 2.09/1.23  tff(c_178, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_155, c_175])).
% 2.09/1.23  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.23  tff(c_136, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_30])).
% 2.09/1.23  tff(c_26, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.23  tff(c_143, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_26])).
% 2.09/1.23  tff(c_203, plain, (![C_48, B_49, A_50]: (C_48=B_49 | k1_funct_1(A_50, C_48)!=k1_funct_1(A_50, B_49) | ~r2_hidden(C_48, k1_relat_1(A_50)) | ~r2_hidden(B_49, k1_relat_1(A_50)) | ~v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.23  tff(c_209, plain, (![B_49]: (B_49='#skF_5' | k1_funct_1('#skF_4', B_49)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_49, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_203])).
% 2.09/1.23  tff(c_216, plain, (![B_51]: (B_51='#skF_5' | k1_funct_1('#skF_4', B_51)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(B_51, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_22, c_132, c_178, c_136, c_178, c_209])).
% 2.09/1.23  tff(c_222, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_134, c_216])).
% 2.09/1.23  tff(c_230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_222])).
% 2.09/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.23  
% 2.09/1.23  Inference rules
% 2.09/1.23  ----------------------
% 2.09/1.23  #Ref     : 3
% 2.09/1.23  #Sup     : 37
% 2.09/1.23  #Fact    : 0
% 2.09/1.23  #Define  : 0
% 2.09/1.23  #Split   : 1
% 2.09/1.23  #Chain   : 0
% 2.09/1.23  #Close   : 0
% 2.09/1.23  
% 2.09/1.23  Ordering : KBO
% 2.09/1.23  
% 2.09/1.23  Simplification rules
% 2.09/1.23  ----------------------
% 2.09/1.23  #Subsume      : 8
% 2.09/1.23  #Demod        : 46
% 2.09/1.23  #Tautology    : 30
% 2.09/1.23  #SimpNegUnit  : 7
% 2.09/1.23  #BackRed      : 2
% 2.09/1.23  
% 2.09/1.23  #Partial instantiations: 0
% 2.09/1.23  #Strategies tried      : 1
% 2.09/1.23  
% 2.09/1.23  Timing (in seconds)
% 2.09/1.23  ----------------------
% 2.09/1.23  Preprocessing        : 0.30
% 2.09/1.23  Parsing              : 0.16
% 2.09/1.23  CNF conversion       : 0.02
% 2.09/1.23  Main loop            : 0.18
% 2.09/1.23  Inferencing          : 0.07
% 2.09/1.23  Reduction            : 0.05
% 2.09/1.23  Demodulation         : 0.04
% 2.09/1.23  BG Simplification    : 0.02
% 2.09/1.23  Subsumption          : 0.02
% 2.09/1.23  Abstraction          : 0.01
% 2.09/1.23  MUC search           : 0.00
% 2.09/1.23  Cooper               : 0.00
% 2.09/1.23  Total                : 0.51
% 2.09/1.23  Index Insertion      : 0.00
% 2.09/1.23  Index Deletion       : 0.00
% 2.09/1.23  Index Matching       : 0.00
% 2.09/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
