%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:28 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   58 (  79 expanded)
%              Number of leaves         :   32 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :   92 ( 178 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_6,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_42,c_48])).

tff(c_54,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_51])).

tff(c_46,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_61,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_65,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_61])).

tff(c_70,plain,(
    ! [A_79,B_80,C_81] :
      ( m1_subset_1(k1_relset_1(A_79,B_80,C_81),k1_zfmisc_1(A_79))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_80,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_70])).

tff(c_84,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_80])).

tff(c_10,plain,(
    ! [A_10,B_33,D_48] :
      ( k1_funct_1(A_10,'#skF_4'(A_10,B_33,k9_relat_1(A_10,B_33),D_48)) = D_48
      | ~ r2_hidden(D_48,k9_relat_1(A_10,B_33))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_137,plain,(
    ! [A_97,B_98,D_99] :
      ( r2_hidden('#skF_4'(A_97,B_98,k9_relat_1(A_97,B_98),D_99),k1_relat_1(A_97))
      | ~ r2_hidden(D_99,k9_relat_1(A_97,B_98))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_97,B_98,D_99,A_1] :
      ( r2_hidden('#skF_4'(A_97,B_98,k9_relat_1(A_97,B_98),D_99),A_1)
      | ~ m1_subset_1(k1_relat_1(A_97),k1_zfmisc_1(A_1))
      | ~ r2_hidden(D_99,k9_relat_1(A_97,B_98))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_128,plain,(
    ! [A_94,B_95,D_96] :
      ( r2_hidden('#skF_4'(A_94,B_95,k9_relat_1(A_94,B_95),D_96),B_95)
      | ~ r2_hidden(D_96,k9_relat_1(A_94,B_95))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    ! [F_66] :
      ( k1_funct_1('#skF_8',F_66) != '#skF_9'
      | ~ r2_hidden(F_66,'#skF_7')
      | ~ r2_hidden(F_66,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_264,plain,(
    ! [A_149,D_150] :
      ( k1_funct_1('#skF_8','#skF_4'(A_149,'#skF_7',k9_relat_1(A_149,'#skF_7'),D_150)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_149,'#skF_7',k9_relat_1(A_149,'#skF_7'),D_150),'#skF_5')
      | ~ r2_hidden(D_150,k9_relat_1(A_149,'#skF_7'))
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_128,c_38])).

tff(c_276,plain,(
    ! [A_151,D_152] :
      ( k1_funct_1('#skF_8','#skF_4'(A_151,'#skF_7',k9_relat_1(A_151,'#skF_7'),D_152)) != '#skF_9'
      | ~ m1_subset_1(k1_relat_1(A_151),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_152,k9_relat_1(A_151,'#skF_7'))
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_140,c_264])).

tff(c_279,plain,(
    ! [D_48] :
      ( D_48 != '#skF_9'
      | ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_48,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_48,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_276])).

tff(c_282,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_54,c_46,c_84,c_279])).

tff(c_90,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k7_relset_1(A_82,B_83,C_84,D_85) = k9_relat_1(C_84,D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_97,plain,(
    ! [D_85] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_85) = k9_relat_1('#skF_8',D_85) ),
    inference(resolution,[status(thm)],[c_42,c_90])).

tff(c_40,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_99,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_40])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:29:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.43  
% 2.35/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.43  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.35/1.43  
% 2.35/1.43  %Foreground sorts:
% 2.35/1.43  
% 2.35/1.43  
% 2.35/1.43  %Background operators:
% 2.35/1.43  
% 2.35/1.43  
% 2.35/1.43  %Foreground operators:
% 2.35/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.35/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.35/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.35/1.43  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.35/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.35/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.35/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.35/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.35/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.35/1.43  tff('#skF_9', type, '#skF_9': $i).
% 2.35/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.35/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.35/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.35/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.35/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.35/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.43  
% 2.35/1.44  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.35/1.44  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 2.35/1.44  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.35/1.44  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.35/1.44  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.35/1.44  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.35/1.44  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.35/1.44  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.35/1.44  tff(c_6, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.35/1.44  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.35/1.44  tff(c_48, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.35/1.44  tff(c_51, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_48])).
% 2.35/1.44  tff(c_54, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_51])).
% 2.35/1.44  tff(c_46, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.35/1.44  tff(c_61, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.35/1.44  tff(c_65, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_61])).
% 2.35/1.44  tff(c_70, plain, (![A_79, B_80, C_81]: (m1_subset_1(k1_relset_1(A_79, B_80, C_81), k1_zfmisc_1(A_79)) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.35/1.44  tff(c_80, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_65, c_70])).
% 2.35/1.44  tff(c_84, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_80])).
% 2.35/1.44  tff(c_10, plain, (![A_10, B_33, D_48]: (k1_funct_1(A_10, '#skF_4'(A_10, B_33, k9_relat_1(A_10, B_33), D_48))=D_48 | ~r2_hidden(D_48, k9_relat_1(A_10, B_33)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.35/1.44  tff(c_137, plain, (![A_97, B_98, D_99]: (r2_hidden('#skF_4'(A_97, B_98, k9_relat_1(A_97, B_98), D_99), k1_relat_1(A_97)) | ~r2_hidden(D_99, k9_relat_1(A_97, B_98)) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.35/1.44  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.35/1.44  tff(c_140, plain, (![A_97, B_98, D_99, A_1]: (r2_hidden('#skF_4'(A_97, B_98, k9_relat_1(A_97, B_98), D_99), A_1) | ~m1_subset_1(k1_relat_1(A_97), k1_zfmisc_1(A_1)) | ~r2_hidden(D_99, k9_relat_1(A_97, B_98)) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_137, c_2])).
% 2.35/1.44  tff(c_128, plain, (![A_94, B_95, D_96]: (r2_hidden('#skF_4'(A_94, B_95, k9_relat_1(A_94, B_95), D_96), B_95) | ~r2_hidden(D_96, k9_relat_1(A_94, B_95)) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.35/1.44  tff(c_38, plain, (![F_66]: (k1_funct_1('#skF_8', F_66)!='#skF_9' | ~r2_hidden(F_66, '#skF_7') | ~r2_hidden(F_66, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.35/1.44  tff(c_264, plain, (![A_149, D_150]: (k1_funct_1('#skF_8', '#skF_4'(A_149, '#skF_7', k9_relat_1(A_149, '#skF_7'), D_150))!='#skF_9' | ~r2_hidden('#skF_4'(A_149, '#skF_7', k9_relat_1(A_149, '#skF_7'), D_150), '#skF_5') | ~r2_hidden(D_150, k9_relat_1(A_149, '#skF_7')) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_128, c_38])).
% 2.35/1.44  tff(c_276, plain, (![A_151, D_152]: (k1_funct_1('#skF_8', '#skF_4'(A_151, '#skF_7', k9_relat_1(A_151, '#skF_7'), D_152))!='#skF_9' | ~m1_subset_1(k1_relat_1(A_151), k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_152, k9_relat_1(A_151, '#skF_7')) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(resolution, [status(thm)], [c_140, c_264])).
% 2.35/1.44  tff(c_279, plain, (![D_48]: (D_48!='#skF_9' | ~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_48, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_48, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_276])).
% 2.35/1.44  tff(c_282, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_54, c_46, c_84, c_279])).
% 2.35/1.44  tff(c_90, plain, (![A_82, B_83, C_84, D_85]: (k7_relset_1(A_82, B_83, C_84, D_85)=k9_relat_1(C_84, D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.35/1.44  tff(c_97, plain, (![D_85]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_85)=k9_relat_1('#skF_8', D_85))), inference(resolution, [status(thm)], [c_42, c_90])).
% 2.35/1.44  tff(c_40, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.35/1.44  tff(c_99, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_40])).
% 2.35/1.44  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_282, c_99])).
% 2.35/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.44  
% 2.35/1.44  Inference rules
% 2.35/1.44  ----------------------
% 2.35/1.44  #Ref     : 0
% 2.35/1.44  #Sup     : 51
% 2.35/1.44  #Fact    : 0
% 2.35/1.44  #Define  : 0
% 2.35/1.44  #Split   : 2
% 2.35/1.44  #Chain   : 0
% 2.35/1.44  #Close   : 0
% 2.35/1.44  
% 2.35/1.44  Ordering : KBO
% 2.35/1.44  
% 2.35/1.44  Simplification rules
% 2.35/1.44  ----------------------
% 2.35/1.44  #Subsume      : 2
% 2.35/1.44  #Demod        : 10
% 2.35/1.44  #Tautology    : 8
% 2.35/1.44  #SimpNegUnit  : 1
% 2.35/1.44  #BackRed      : 3
% 2.35/1.44  
% 2.35/1.44  #Partial instantiations: 0
% 2.35/1.44  #Strategies tried      : 1
% 2.35/1.44  
% 2.35/1.44  Timing (in seconds)
% 2.35/1.44  ----------------------
% 2.35/1.45  Preprocessing        : 0.38
% 2.35/1.45  Parsing              : 0.20
% 2.35/1.45  CNF conversion       : 0.03
% 2.35/1.45  Main loop            : 0.24
% 2.35/1.45  Inferencing          : 0.09
% 2.35/1.45  Reduction            : 0.06
% 2.35/1.45  Demodulation         : 0.05
% 2.35/1.45  BG Simplification    : 0.02
% 2.35/1.45  Subsumption          : 0.05
% 2.35/1.45  Abstraction          : 0.02
% 2.35/1.45  MUC search           : 0.00
% 2.35/1.45  Cooper               : 0.00
% 2.35/1.45  Total                : 0.65
% 2.35/1.45  Index Insertion      : 0.00
% 2.35/1.45  Index Deletion       : 0.00
% 2.35/1.45  Index Matching       : 0.00
% 2.35/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
