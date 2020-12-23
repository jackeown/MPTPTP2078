%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:32 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 183 expanded)
%              Number of leaves         :   34 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 376 expanded)
%              Number of equality atoms :   19 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_51,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_57,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_54])).

tff(c_48,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58,plain,(
    ! [C_65,A_66,B_67] :
      ( v4_relat_1(C_65,A_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_62,plain,(
    v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_58])).

tff(c_72,plain,(
    ! [B_70,A_71] :
      ( k7_relat_1(B_70,A_71) = B_70
      | ~ v4_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,
    ( k7_relat_1('#skF_8','#skF_5') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_72])).

tff(c_78,plain,(
    k7_relat_1('#skF_8','#skF_5') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_75])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,
    ( k9_relat_1('#skF_8','#skF_5') = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_6])).

tff(c_86,plain,(
    k9_relat_1('#skF_8','#skF_5') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_82])).

tff(c_131,plain,(
    ! [A_87,B_88,D_89] :
      ( k1_funct_1(A_87,'#skF_4'(A_87,B_88,k9_relat_1(A_87,B_88),D_89)) = D_89
      | ~ r2_hidden(D_89,k9_relat_1(A_87,B_88))
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_147,plain,(
    ! [D_89] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_5',k2_relat_1('#skF_8'),D_89)) = D_89
      | ~ r2_hidden(D_89,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_131])).

tff(c_160,plain,(
    ! [D_93] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_5',k2_relat_1('#skF_8'),D_93)) = D_93
      | ~ r2_hidden(D_93,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_48,c_86,c_147])).

tff(c_114,plain,(
    ! [A_82,B_83,D_84] :
      ( r2_hidden('#skF_4'(A_82,B_83,k9_relat_1(A_82,B_83),D_84),B_83)
      | ~ r2_hidden(D_84,k9_relat_1(A_82,B_83))
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_121,plain,(
    ! [D_84] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_5',k2_relat_1('#skF_8'),D_84),'#skF_5')
      | ~ r2_hidden(D_84,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_114])).

tff(c_125,plain,(
    ! [D_85] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_5',k2_relat_1('#skF_8'),D_85),'#skF_5')
      | ~ r2_hidden(D_85,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_48,c_86,c_121])).

tff(c_40,plain,(
    ! [E_59] :
      ( k1_funct_1('#skF_8',E_59) != '#skF_7'
      | ~ r2_hidden(E_59,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_129,plain,(
    ! [D_85] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_5',k2_relat_1('#skF_8'),D_85)) != '#skF_7'
      | ~ r2_hidden(D_85,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_125,c_40])).

tff(c_180,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_129])).

tff(c_97,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_101,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_97])).

tff(c_42,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_102,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_42])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:42:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.17/1.31  
% 2.17/1.31  %Foreground sorts:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Background operators:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Foreground operators:
% 2.17/1.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.17/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.17/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.17/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.17/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.17/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.17/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.17/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.17/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.31  
% 2.17/1.33  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.17/1.33  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.17/1.33  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.33  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.17/1.33  tff(f_44, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.17/1.33  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.17/1.33  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 2.17/1.33  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.17/1.33  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.33  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.17/1.33  tff(c_51, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.33  tff(c_54, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_51])).
% 2.17/1.33  tff(c_57, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_54])).
% 2.17/1.33  tff(c_48, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.17/1.33  tff(c_58, plain, (![C_65, A_66, B_67]: (v4_relat_1(C_65, A_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.17/1.33  tff(c_62, plain, (v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_58])).
% 2.17/1.33  tff(c_72, plain, (![B_70, A_71]: (k7_relat_1(B_70, A_71)=B_70 | ~v4_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.33  tff(c_75, plain, (k7_relat_1('#skF_8', '#skF_5')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_72])).
% 2.17/1.33  tff(c_78, plain, (k7_relat_1('#skF_8', '#skF_5')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_75])).
% 2.17/1.33  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.17/1.33  tff(c_82, plain, (k9_relat_1('#skF_8', '#skF_5')=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_78, c_6])).
% 2.17/1.33  tff(c_86, plain, (k9_relat_1('#skF_8', '#skF_5')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_82])).
% 2.17/1.33  tff(c_131, plain, (![A_87, B_88, D_89]: (k1_funct_1(A_87, '#skF_4'(A_87, B_88, k9_relat_1(A_87, B_88), D_89))=D_89 | ~r2_hidden(D_89, k9_relat_1(A_87, B_88)) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.33  tff(c_147, plain, (![D_89]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_5', k2_relat_1('#skF_8'), D_89))=D_89 | ~r2_hidden(D_89, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_131])).
% 2.17/1.33  tff(c_160, plain, (![D_93]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_5', k2_relat_1('#skF_8'), D_93))=D_93 | ~r2_hidden(D_93, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_48, c_86, c_147])).
% 2.17/1.33  tff(c_114, plain, (![A_82, B_83, D_84]: (r2_hidden('#skF_4'(A_82, B_83, k9_relat_1(A_82, B_83), D_84), B_83) | ~r2_hidden(D_84, k9_relat_1(A_82, B_83)) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.33  tff(c_121, plain, (![D_84]: (r2_hidden('#skF_4'('#skF_8', '#skF_5', k2_relat_1('#skF_8'), D_84), '#skF_5') | ~r2_hidden(D_84, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_114])).
% 2.17/1.33  tff(c_125, plain, (![D_85]: (r2_hidden('#skF_4'('#skF_8', '#skF_5', k2_relat_1('#skF_8'), D_85), '#skF_5') | ~r2_hidden(D_85, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_48, c_86, c_121])).
% 2.17/1.33  tff(c_40, plain, (![E_59]: (k1_funct_1('#skF_8', E_59)!='#skF_7' | ~r2_hidden(E_59, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.17/1.33  tff(c_129, plain, (![D_85]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_5', k2_relat_1('#skF_8'), D_85))!='#skF_7' | ~r2_hidden(D_85, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_125, c_40])).
% 2.17/1.33  tff(c_180, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_160, c_129])).
% 2.17/1.33  tff(c_97, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.33  tff(c_101, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_97])).
% 2.17/1.33  tff(c_42, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.17/1.33  tff(c_102, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_42])).
% 2.17/1.33  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_102])).
% 2.17/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.33  
% 2.17/1.33  Inference rules
% 2.17/1.33  ----------------------
% 2.17/1.33  #Ref     : 0
% 2.17/1.33  #Sup     : 29
% 2.17/1.33  #Fact    : 0
% 2.17/1.33  #Define  : 0
% 2.17/1.33  #Split   : 0
% 2.17/1.33  #Chain   : 0
% 2.17/1.33  #Close   : 0
% 2.17/1.33  
% 2.17/1.33  Ordering : KBO
% 2.17/1.33  
% 2.17/1.33  Simplification rules
% 2.17/1.33  ----------------------
% 2.17/1.33  #Subsume      : 0
% 2.17/1.33  #Demod        : 19
% 2.17/1.33  #Tautology    : 13
% 2.17/1.33  #SimpNegUnit  : 1
% 2.17/1.33  #BackRed      : 2
% 2.17/1.33  
% 2.17/1.33  #Partial instantiations: 0
% 2.17/1.33  #Strategies tried      : 1
% 2.17/1.33  
% 2.17/1.33  Timing (in seconds)
% 2.17/1.33  ----------------------
% 2.17/1.33  Preprocessing        : 0.34
% 2.17/1.33  Parsing              : 0.17
% 2.17/1.33  CNF conversion       : 0.03
% 2.17/1.33  Main loop            : 0.15
% 2.17/1.33  Inferencing          : 0.06
% 2.17/1.33  Reduction            : 0.05
% 2.17/1.33  Demodulation         : 0.04
% 2.17/1.33  BG Simplification    : 0.02
% 2.17/1.33  Subsumption          : 0.02
% 2.17/1.33  Abstraction          : 0.01
% 2.17/1.33  MUC search           : 0.00
% 2.17/1.33  Cooper               : 0.00
% 2.17/1.33  Total                : 0.52
% 2.17/1.33  Index Insertion      : 0.00
% 2.17/1.33  Index Deletion       : 0.00
% 2.17/1.33  Index Matching       : 0.00
% 2.17/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
