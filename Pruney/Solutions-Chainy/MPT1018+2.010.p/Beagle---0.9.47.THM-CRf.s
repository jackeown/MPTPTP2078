%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:46 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 312 expanded)
%              Number of leaves         :   30 ( 136 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 (1155 expanded)
%              Number of equality atoms :   23 ( 270 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

tff(c_40,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_61,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_65,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_61])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_48,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_66,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_relset_1(A_34,B_35,C_36) = k1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_70,plain,(
    k1_relset_1('#skF_5','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_66])).

tff(c_80,plain,(
    ! [A_38,B_39] :
      ( k1_relset_1(A_38,A_38,B_39) = A_38
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_zfmisc_1(A_38,A_38)))
      | ~ v1_funct_2(B_39,A_38,A_38)
      | ~ v1_funct_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_83,plain,
    ( k1_relset_1('#skF_5','#skF_5','#skF_6') = '#skF_5'
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_80])).

tff(c_86,plain,(
    k1_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_70,c_83])).

tff(c_42,plain,(
    k1_funct_1('#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_101,plain,(
    ! [A_41,D_42] :
      ( r2_hidden(k1_funct_1(A_41,D_42),k2_relat_1(A_41))
      | ~ r2_hidden(D_42,k1_relat_1(A_41))
      | ~ v1_funct_1(k2_funct_1(A_41))
      | ~ v1_relat_1(k2_funct_1(A_41))
      | ~ v2_funct_1(A_41)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_104,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_8'),k2_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_101])).

tff(c_106,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_8'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54,c_48,c_46,c_86,c_104])).

tff(c_116,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_119,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54,c_119])).

tff(c_125,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_124,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | r2_hidden(k1_funct_1('#skF_6','#skF_8'),k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_126,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_149,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_126])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54,c_149])).

tff(c_155,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_44,plain,(
    r2_hidden('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_166,plain,(
    ! [A_49,D_50] :
      ( k1_funct_1(k2_funct_1(A_49),k1_funct_1(A_49,D_50)) = D_50
      | ~ r2_hidden(D_50,k1_relat_1(A_49))
      | ~ v1_funct_1(k2_funct_1(A_49))
      | ~ v1_relat_1(k2_funct_1(A_49))
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_191,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_8')) = '#skF_7'
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_166])).

tff(c_197,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54,c_48,c_125,c_155,c_46,c_86,c_191])).

tff(c_30,plain,(
    ! [A_2,D_18] :
      ( k1_funct_1(k2_funct_1(A_2),k1_funct_1(A_2,D_18)) = D_18
      | ~ r2_hidden(D_18,k1_relat_1(A_2))
      | ~ v1_funct_1(k2_funct_1(A_2))
      | ~ v1_relat_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_204,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_30])).

tff(c_222,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54,c_48,c_125,c_155,c_44,c_86,c_204])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:36:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.12/1.30  
% 2.12/1.30  %Foreground sorts:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Background operators:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Foreground operators:
% 2.12/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.12/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.12/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.12/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.12/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.12/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.12/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.12/1.30  tff('#skF_8', type, '#skF_8': $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.12/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.30  
% 2.40/1.31  tff(f_99, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.40/1.31  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.40/1.31  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.40/1.31  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.40/1.31  tff(f_81, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 2.40/1.31  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 2.40/1.31  tff(c_40, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.40/1.31  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.40/1.31  tff(c_61, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.40/1.31  tff(c_65, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_61])).
% 2.40/1.31  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.40/1.31  tff(c_48, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.40/1.31  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.40/1.31  tff(c_46, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.40/1.31  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.40/1.31  tff(c_66, plain, (![A_34, B_35, C_36]: (k1_relset_1(A_34, B_35, C_36)=k1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.31  tff(c_70, plain, (k1_relset_1('#skF_5', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_66])).
% 2.40/1.31  tff(c_80, plain, (![A_38, B_39]: (k1_relset_1(A_38, A_38, B_39)=A_38 | ~m1_subset_1(B_39, k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))) | ~v1_funct_2(B_39, A_38, A_38) | ~v1_funct_1(B_39))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.40/1.31  tff(c_83, plain, (k1_relset_1('#skF_5', '#skF_5', '#skF_6')='#skF_5' | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_80])).
% 2.40/1.31  tff(c_86, plain, (k1_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_70, c_83])).
% 2.40/1.31  tff(c_42, plain, (k1_funct_1('#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.40/1.31  tff(c_101, plain, (![A_41, D_42]: (r2_hidden(k1_funct_1(A_41, D_42), k2_relat_1(A_41)) | ~r2_hidden(D_42, k1_relat_1(A_41)) | ~v1_funct_1(k2_funct_1(A_41)) | ~v1_relat_1(k2_funct_1(A_41)) | ~v2_funct_1(A_41) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.31  tff(c_104, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_42, c_101])).
% 2.40/1.31  tff(c_106, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_54, c_48, c_46, c_86, c_104])).
% 2.40/1.31  tff(c_116, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_106])).
% 2.40/1.31  tff(c_119, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_116])).
% 2.40/1.31  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_54, c_119])).
% 2.40/1.31  tff(c_125, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_106])).
% 2.40/1.31  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.40/1.31  tff(c_124, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_106])).
% 2.40/1.31  tff(c_126, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_124])).
% 2.40/1.31  tff(c_149, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_126])).
% 2.40/1.31  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_54, c_149])).
% 2.40/1.31  tff(c_155, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_124])).
% 2.40/1.31  tff(c_44, plain, (r2_hidden('#skF_8', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.40/1.31  tff(c_166, plain, (![A_49, D_50]: (k1_funct_1(k2_funct_1(A_49), k1_funct_1(A_49, D_50))=D_50 | ~r2_hidden(D_50, k1_relat_1(A_49)) | ~v1_funct_1(k2_funct_1(A_49)) | ~v1_relat_1(k2_funct_1(A_49)) | ~v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.31  tff(c_191, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_8'))='#skF_7' | ~r2_hidden('#skF_7', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_42, c_166])).
% 2.40/1.31  tff(c_197, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_54, c_48, c_125, c_155, c_46, c_86, c_191])).
% 2.40/1.31  tff(c_30, plain, (![A_2, D_18]: (k1_funct_1(k2_funct_1(A_2), k1_funct_1(A_2, D_18))=D_18 | ~r2_hidden(D_18, k1_relat_1(A_2)) | ~v1_funct_1(k2_funct_1(A_2)) | ~v1_relat_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.31  tff(c_204, plain, ('#skF_7'='#skF_8' | ~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_197, c_30])).
% 2.40/1.31  tff(c_222, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_54, c_48, c_125, c_155, c_44, c_86, c_204])).
% 2.40/1.31  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_222])).
% 2.40/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.31  
% 2.40/1.31  Inference rules
% 2.40/1.31  ----------------------
% 2.40/1.31  #Ref     : 0
% 2.40/1.31  #Sup     : 41
% 2.40/1.31  #Fact    : 0
% 2.40/1.31  #Define  : 0
% 2.40/1.31  #Split   : 2
% 2.40/1.31  #Chain   : 0
% 2.40/1.31  #Close   : 0
% 2.40/1.31  
% 2.40/1.31  Ordering : KBO
% 2.40/1.31  
% 2.40/1.31  Simplification rules
% 2.40/1.31  ----------------------
% 2.40/1.31  #Subsume      : 2
% 2.40/1.31  #Demod        : 40
% 2.40/1.31  #Tautology    : 18
% 2.40/1.31  #SimpNegUnit  : 1
% 2.40/1.31  #BackRed      : 1
% 2.40/1.31  
% 2.40/1.31  #Partial instantiations: 0
% 2.40/1.31  #Strategies tried      : 1
% 2.40/1.31  
% 2.40/1.31  Timing (in seconds)
% 2.40/1.31  ----------------------
% 2.40/1.32  Preprocessing        : 0.34
% 2.40/1.32  Parsing              : 0.17
% 2.40/1.32  CNF conversion       : 0.03
% 2.40/1.32  Main loop            : 0.21
% 2.40/1.32  Inferencing          : 0.07
% 2.40/1.32  Reduction            : 0.06
% 2.40/1.32  Demodulation         : 0.05
% 2.40/1.32  BG Simplification    : 0.02
% 2.40/1.32  Subsumption          : 0.04
% 2.40/1.32  Abstraction          : 0.01
% 2.40/1.32  MUC search           : 0.00
% 2.40/1.32  Cooper               : 0.00
% 2.40/1.32  Total                : 0.58
% 2.40/1.32  Index Insertion      : 0.00
% 2.40/1.32  Index Deletion       : 0.00
% 2.40/1.32  Index Matching       : 0.00
% 2.40/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
