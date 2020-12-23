%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:03 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 108 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  100 ( 308 expanded)
%              Number of equality atoms :   11 (  21 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( r2_hidden(D,k5_partfun1(A,B,C))
           => ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_49,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_44,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_65,plain,(
    ! [A_55,B_56,C_57,E_58] :
      ( '#skF_4'(k5_partfun1(A_55,B_56,C_57),E_58,B_56,C_57,A_55) = E_58
      | ~ r2_hidden(E_58,k5_partfun1(A_55,B_56,C_57))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ v1_funct_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_67,plain,
    ( '#skF_4'(k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_8','#skF_6','#skF_7','#skF_5') = '#skF_8'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_65])).

tff(c_70,plain,(
    '#skF_4'(k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_8','#skF_6','#skF_7','#skF_5') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_67])).

tff(c_58,plain,(
    ! [A_50,B_51,C_52,E_53] :
      ( v1_funct_1('#skF_4'(k5_partfun1(A_50,B_51,C_52),E_53,B_51,C_52,A_50))
      | ~ r2_hidden(E_53,k5_partfun1(A_50,B_51,C_52))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,(
    ! [E_53] :
      ( v1_funct_1('#skF_4'(k5_partfun1('#skF_5','#skF_6','#skF_7'),E_53,'#skF_6','#skF_7','#skF_5'))
      | ~ r2_hidden(E_53,k5_partfun1('#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_58])).

tff(c_63,plain,(
    ! [E_53] :
      ( v1_funct_1('#skF_4'(k5_partfun1('#skF_5','#skF_6','#skF_7'),E_53,'#skF_6','#skF_7','#skF_5'))
      | ~ r2_hidden(E_53,k5_partfun1('#skF_5','#skF_6','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_60])).

tff(c_74,plain,
    ( v1_funct_1('#skF_8')
    | ~ r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_63])).

tff(c_78,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_74])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_78])).

tff(c_81,plain,
    ( ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_83,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_99,plain,(
    ! [A_67,B_68,C_69,E_70] :
      ( '#skF_4'(k5_partfun1(A_67,B_68,C_69),E_70,B_68,C_69,A_67) = E_70
      | ~ r2_hidden(E_70,k5_partfun1(A_67,B_68,C_69))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_101,plain,
    ( '#skF_4'(k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_8','#skF_6','#skF_7','#skF_5') = '#skF_8'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_99])).

tff(c_104,plain,(
    '#skF_4'(k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_8','#skF_6','#skF_7','#skF_5') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_101])).

tff(c_170,plain,(
    ! [A_99,B_100,C_101,E_102] :
      ( m1_subset_1('#skF_4'(k5_partfun1(A_99,B_100,C_101),E_102,B_100,C_101,A_99),k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ r2_hidden(E_102,k5_partfun1(A_99,B_100,C_101))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_186,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_170])).

tff(c_194,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_186])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_194])).

tff(c_197,plain,(
    ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_82,plain,(
    v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_198,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_199,plain,(
    ! [C_103,A_104,B_105] :
      ( v1_funct_2(C_103,A_104,B_105)
      | ~ v1_partfun1(C_103,A_104)
      | ~ v1_funct_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_202,plain,
    ( v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_partfun1('#skF_8','#skF_5')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_198,c_199])).

tff(c_208,plain,
    ( v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_partfun1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_202])).

tff(c_209,plain,(
    ~ v1_partfun1('#skF_8','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_208])).

tff(c_227,plain,(
    ! [A_112,B_113,C_114,E_115] :
      ( '#skF_4'(k5_partfun1(A_112,B_113,C_114),E_115,B_113,C_114,A_112) = E_115
      | ~ r2_hidden(E_115,k5_partfun1(A_112,B_113,C_114))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_funct_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_229,plain,
    ( '#skF_4'(k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_8','#skF_6','#skF_7','#skF_5') = '#skF_8'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_227])).

tff(c_232,plain,(
    '#skF_4'(k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_8','#skF_6','#skF_7','#skF_5') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_229])).

tff(c_248,plain,(
    ! [A_120,B_121,C_122,E_123] :
      ( v1_partfun1('#skF_4'(k5_partfun1(A_120,B_121,C_122),E_123,B_121,C_122,A_120),A_120)
      | ~ r2_hidden(E_123,k5_partfun1(A_120,B_121,C_122))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_251,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | ~ r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_248])).

tff(c_253,plain,(
    v1_partfun1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_251])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.26  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 2.17/1.26  
% 2.17/1.26  %Foreground sorts:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Background operators:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Foreground operators:
% 2.17/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.17/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.17/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.17/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.26  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.17/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.26  tff('#skF_8', type, '#skF_8': $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.17/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.17/1.26  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 2.17/1.26  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.17/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.26  
% 2.17/1.28  tff(f_70, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (r2_hidden(D, k5_partfun1(A, B, C)) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 2.17/1.28  tff(f_56, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 2.17/1.28  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 2.17/1.28  tff(c_42, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.28  tff(c_49, plain, (~v1_funct_1('#skF_8')), inference(splitLeft, [status(thm)], [c_42])).
% 2.17/1.28  tff(c_44, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.28  tff(c_48, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.28  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.28  tff(c_65, plain, (![A_55, B_56, C_57, E_58]: ('#skF_4'(k5_partfun1(A_55, B_56, C_57), E_58, B_56, C_57, A_55)=E_58 | ~r2_hidden(E_58, k5_partfun1(A_55, B_56, C_57)) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~v1_funct_1(C_57))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.28  tff(c_67, plain, ('#skF_4'(k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_8', '#skF_6', '#skF_7', '#skF_5')='#skF_8' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_65])).
% 2.17/1.28  tff(c_70, plain, ('#skF_4'(k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_8', '#skF_6', '#skF_7', '#skF_5')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_67])).
% 2.17/1.28  tff(c_58, plain, (![A_50, B_51, C_52, E_53]: (v1_funct_1('#skF_4'(k5_partfun1(A_50, B_51, C_52), E_53, B_51, C_52, A_50)) | ~r2_hidden(E_53, k5_partfun1(A_50, B_51, C_52)) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~v1_funct_1(C_52))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.28  tff(c_60, plain, (![E_53]: (v1_funct_1('#skF_4'(k5_partfun1('#skF_5', '#skF_6', '#skF_7'), E_53, '#skF_6', '#skF_7', '#skF_5')) | ~r2_hidden(E_53, k5_partfun1('#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_46, c_58])).
% 2.17/1.28  tff(c_63, plain, (![E_53]: (v1_funct_1('#skF_4'(k5_partfun1('#skF_5', '#skF_6', '#skF_7'), E_53, '#skF_6', '#skF_7', '#skF_5')) | ~r2_hidden(E_53, k5_partfun1('#skF_5', '#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_60])).
% 2.17/1.28  tff(c_74, plain, (v1_funct_1('#skF_8') | ~r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_63])).
% 2.17/1.28  tff(c_78, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_74])).
% 2.17/1.28  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_78])).
% 2.17/1.28  tff(c_81, plain, (~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_42])).
% 2.17/1.28  tff(c_83, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_81])).
% 2.17/1.28  tff(c_99, plain, (![A_67, B_68, C_69, E_70]: ('#skF_4'(k5_partfun1(A_67, B_68, C_69), E_70, B_68, C_69, A_67)=E_70 | ~r2_hidden(E_70, k5_partfun1(A_67, B_68, C_69)) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_1(C_69))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.28  tff(c_101, plain, ('#skF_4'(k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_8', '#skF_6', '#skF_7', '#skF_5')='#skF_8' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_99])).
% 2.17/1.28  tff(c_104, plain, ('#skF_4'(k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_8', '#skF_6', '#skF_7', '#skF_5')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_101])).
% 2.17/1.28  tff(c_170, plain, (![A_99, B_100, C_101, E_102]: (m1_subset_1('#skF_4'(k5_partfun1(A_99, B_100, C_101), E_102, B_100, C_101, A_99), k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~r2_hidden(E_102, k5_partfun1(A_99, B_100, C_101)) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_1(C_101))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.28  tff(c_186, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_104, c_170])).
% 2.17/1.28  tff(c_194, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_186])).
% 2.17/1.28  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_194])).
% 2.17/1.28  tff(c_197, plain, (~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_81])).
% 2.17/1.28  tff(c_82, plain, (v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_42])).
% 2.17/1.28  tff(c_198, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_81])).
% 2.17/1.28  tff(c_199, plain, (![C_103, A_104, B_105]: (v1_funct_2(C_103, A_104, B_105) | ~v1_partfun1(C_103, A_104) | ~v1_funct_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.28  tff(c_202, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_198, c_199])).
% 2.17/1.28  tff(c_208, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_partfun1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_202])).
% 2.17/1.28  tff(c_209, plain, (~v1_partfun1('#skF_8', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_197, c_208])).
% 2.17/1.28  tff(c_227, plain, (![A_112, B_113, C_114, E_115]: ('#skF_4'(k5_partfun1(A_112, B_113, C_114), E_115, B_113, C_114, A_112)=E_115 | ~r2_hidden(E_115, k5_partfun1(A_112, B_113, C_114)) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~v1_funct_1(C_114))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.28  tff(c_229, plain, ('#skF_4'(k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_8', '#skF_6', '#skF_7', '#skF_5')='#skF_8' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_227])).
% 2.17/1.28  tff(c_232, plain, ('#skF_4'(k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_8', '#skF_6', '#skF_7', '#skF_5')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_229])).
% 2.17/1.28  tff(c_248, plain, (![A_120, B_121, C_122, E_123]: (v1_partfun1('#skF_4'(k5_partfun1(A_120, B_121, C_122), E_123, B_121, C_122, A_120), A_120) | ~r2_hidden(E_123, k5_partfun1(A_120, B_121, C_122)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(C_122))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.28  tff(c_251, plain, (v1_partfun1('#skF_8', '#skF_5') | ~r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_232, c_248])).
% 2.17/1.28  tff(c_253, plain, (v1_partfun1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_251])).
% 2.17/1.28  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_253])).
% 2.17/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.28  
% 2.17/1.28  Inference rules
% 2.17/1.28  ----------------------
% 2.17/1.28  #Ref     : 0
% 2.17/1.28  #Sup     : 39
% 2.17/1.28  #Fact    : 0
% 2.17/1.28  #Define  : 0
% 2.17/1.28  #Split   : 5
% 2.17/1.28  #Chain   : 0
% 2.17/1.28  #Close   : 0
% 2.17/1.28  
% 2.17/1.28  Ordering : KBO
% 2.17/1.28  
% 2.17/1.28  Simplification rules
% 2.17/1.28  ----------------------
% 2.17/1.28  #Subsume      : 0
% 2.17/1.28  #Demod        : 38
% 2.17/1.28  #Tautology    : 8
% 2.17/1.28  #SimpNegUnit  : 4
% 2.17/1.28  #BackRed      : 0
% 2.17/1.28  
% 2.17/1.28  #Partial instantiations: 0
% 2.17/1.28  #Strategies tried      : 1
% 2.17/1.28  
% 2.17/1.28  Timing (in seconds)
% 2.17/1.28  ----------------------
% 2.17/1.28  Preprocessing        : 0.32
% 2.17/1.28  Parsing              : 0.15
% 2.17/1.28  CNF conversion       : 0.03
% 2.17/1.28  Main loop            : 0.21
% 2.17/1.28  Inferencing          : 0.08
% 2.17/1.28  Reduction            : 0.06
% 2.17/1.28  Demodulation         : 0.05
% 2.17/1.28  BG Simplification    : 0.02
% 2.17/1.28  Subsumption          : 0.03
% 2.17/1.28  Abstraction          : 0.02
% 2.17/1.28  MUC search           : 0.00
% 2.17/1.28  Cooper               : 0.00
% 2.17/1.28  Total                : 0.56
% 2.17/1.28  Index Insertion      : 0.00
% 2.17/1.28  Index Deletion       : 0.00
% 2.17/1.28  Index Matching       : 0.00
% 2.17/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
