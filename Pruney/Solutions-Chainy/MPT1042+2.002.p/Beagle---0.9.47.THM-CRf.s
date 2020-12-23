%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:03 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 108 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  101 ( 309 expanded)
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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( r2_hidden(D,k5_partfun1(A,B,C))
           => ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

tff(f_46,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_funct_2)).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_51,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_50,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_60,plain,(
    ! [B_50,E_51,A_52,C_53] :
      ( '#skF_4'(B_50,E_51,k5_partfun1(A_52,B_50,C_53),C_53,A_52) = E_51
      | ~ r2_hidden(E_51,k5_partfun1(A_52,B_50,C_53))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_52,B_50)))
      | ~ v1_funct_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,
    ( '#skF_4'('#skF_6','#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_7','#skF_5') = '#skF_8'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_60])).

tff(c_65,plain,(
    '#skF_4'('#skF_6','#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_7','#skF_5') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_62])).

tff(c_70,plain,(
    ! [B_54,E_55,A_56,C_57] :
      ( v1_funct_1('#skF_4'(B_54,E_55,k5_partfun1(A_56,B_54,C_57),C_57,A_56))
      | ~ r2_hidden(E_55,k5_partfun1(A_56,B_54,C_57))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_56,B_54)))
      | ~ v1_funct_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    ! [E_55] :
      ( v1_funct_1('#skF_4'('#skF_6',E_55,k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_7','#skF_5'))
      | ~ r2_hidden(E_55,k5_partfun1('#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_48,c_70])).

tff(c_76,plain,(
    ! [E_58] :
      ( v1_funct_1('#skF_4'('#skF_6',E_58,k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_7','#skF_5'))
      | ~ r2_hidden(E_58,k5_partfun1('#skF_5','#skF_6','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_72])).

tff(c_79,plain,
    ( v1_funct_1('#skF_8')
    | ~ r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_76])).

tff(c_81,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79])).

tff(c_83,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_81])).

tff(c_84,plain,
    ( ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_86,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_102,plain,(
    ! [B_67,E_68,A_69,C_70] :
      ( '#skF_4'(B_67,E_68,k5_partfun1(A_69,B_67,C_70),C_70,A_69) = E_68
      | ~ r2_hidden(E_68,k5_partfun1(A_69,B_67,C_70))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_67)))
      | ~ v1_funct_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_104,plain,
    ( '#skF_4'('#skF_6','#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_7','#skF_5') = '#skF_8'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_102])).

tff(c_107,plain,(
    '#skF_4'('#skF_6','#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_7','#skF_5') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_104])).

tff(c_179,plain,(
    ! [B_103,E_104,A_105,C_106] :
      ( m1_subset_1('#skF_4'(B_103,E_104,k5_partfun1(A_105,B_103,C_106),C_106,A_105),k1_zfmisc_1(k2_zfmisc_1(A_105,B_103)))
      | ~ r2_hidden(E_104,k5_partfun1(A_105,B_103,C_106))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_105,B_103)))
      | ~ v1_funct_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_197,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_179])).

tff(c_206,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_197])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_206])).

tff(c_209,plain,(
    ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_85,plain,(
    v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_210,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_211,plain,(
    ! [C_107,A_108,B_109] :
      ( v1_funct_2(C_107,A_108,B_109)
      | ~ v1_partfun1(C_107,A_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_214,plain,
    ( v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_partfun1('#skF_8','#skF_5')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_210,c_211])).

tff(c_220,plain,
    ( v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_partfun1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_214])).

tff(c_221,plain,(
    ~ v1_partfun1('#skF_8','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_220])).

tff(c_226,plain,(
    ! [B_110,E_111,A_112,C_113] :
      ( '#skF_4'(B_110,E_111,k5_partfun1(A_112,B_110,C_113),C_113,A_112) = E_111
      | ~ r2_hidden(E_111,k5_partfun1(A_112,B_110,C_113))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_112,B_110)))
      | ~ v1_funct_1(C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_228,plain,
    ( '#skF_4'('#skF_6','#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_7','#skF_5') = '#skF_8'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_226])).

tff(c_231,plain,(
    '#skF_4'('#skF_6','#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'),'#skF_7','#skF_5') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_228])).

tff(c_260,plain,(
    ! [B_124,E_125,A_126,C_127] :
      ( v1_partfun1('#skF_4'(B_124,E_125,k5_partfun1(A_126,B_124,C_127),C_127,A_126),A_126)
      | ~ r2_hidden(E_125,k5_partfun1(A_126,B_124,C_127))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_124)))
      | ~ v1_funct_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_263,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | ~ r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_260])).

tff(c_265,plain,(
    v1_partfun1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_263])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:46:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  
% 2.16/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 2.16/1.32  
% 2.16/1.32  %Foreground sorts:
% 2.16/1.32  
% 2.16/1.32  
% 2.16/1.32  %Background operators:
% 2.16/1.32  
% 2.16/1.32  
% 2.16/1.32  %Foreground operators:
% 2.16/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.16/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.16/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.16/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.16/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.16/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.32  tff('#skF_8', type, '#skF_8': $i).
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.16/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.16/1.32  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 2.16/1.32  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.16/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.32  
% 2.37/1.34  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (r2_hidden(D, k5_partfun1(A, B, C)) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_2)).
% 2.37/1.34  tff(f_46, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_partfun1)).
% 2.37/1.34  tff(f_58, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_funct_2)).
% 2.37/1.34  tff(c_44, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.37/1.34  tff(c_51, plain, (~v1_funct_1('#skF_8')), inference(splitLeft, [status(thm)], [c_44])).
% 2.37/1.34  tff(c_46, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.37/1.34  tff(c_50, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.37/1.34  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.37/1.34  tff(c_60, plain, (![B_50, E_51, A_52, C_53]: ('#skF_4'(B_50, E_51, k5_partfun1(A_52, B_50, C_53), C_53, A_52)=E_51 | ~r2_hidden(E_51, k5_partfun1(A_52, B_50, C_53)) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_52, B_50))) | ~v1_funct_1(C_53))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.34  tff(c_62, plain, ('#skF_4'('#skF_6', '#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_7', '#skF_5')='#skF_8' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_46, c_60])).
% 2.37/1.34  tff(c_65, plain, ('#skF_4'('#skF_6', '#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_7', '#skF_5')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_62])).
% 2.37/1.34  tff(c_70, plain, (![B_54, E_55, A_56, C_57]: (v1_funct_1('#skF_4'(B_54, E_55, k5_partfun1(A_56, B_54, C_57), C_57, A_56)) | ~r2_hidden(E_55, k5_partfun1(A_56, B_54, C_57)) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_56, B_54))) | ~v1_funct_1(C_57))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.34  tff(c_72, plain, (![E_55]: (v1_funct_1('#skF_4'('#skF_6', E_55, k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_7', '#skF_5')) | ~r2_hidden(E_55, k5_partfun1('#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_48, c_70])).
% 2.37/1.34  tff(c_76, plain, (![E_58]: (v1_funct_1('#skF_4'('#skF_6', E_58, k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_7', '#skF_5')) | ~r2_hidden(E_58, k5_partfun1('#skF_5', '#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_72])).
% 2.37/1.34  tff(c_79, plain, (v1_funct_1('#skF_8') | ~r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_76])).
% 2.37/1.34  tff(c_81, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79])).
% 2.37/1.34  tff(c_83, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_81])).
% 2.37/1.34  tff(c_84, plain, (~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_44])).
% 2.37/1.34  tff(c_86, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_84])).
% 2.37/1.34  tff(c_102, plain, (![B_67, E_68, A_69, C_70]: ('#skF_4'(B_67, E_68, k5_partfun1(A_69, B_67, C_70), C_70, A_69)=E_68 | ~r2_hidden(E_68, k5_partfun1(A_69, B_67, C_70)) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_67))) | ~v1_funct_1(C_70))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.34  tff(c_104, plain, ('#skF_4'('#skF_6', '#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_7', '#skF_5')='#skF_8' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_46, c_102])).
% 2.37/1.34  tff(c_107, plain, ('#skF_4'('#skF_6', '#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_7', '#skF_5')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_104])).
% 2.37/1.34  tff(c_179, plain, (![B_103, E_104, A_105, C_106]: (m1_subset_1('#skF_4'(B_103, E_104, k5_partfun1(A_105, B_103, C_106), C_106, A_105), k1_zfmisc_1(k2_zfmisc_1(A_105, B_103))) | ~r2_hidden(E_104, k5_partfun1(A_105, B_103, C_106)) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_105, B_103))) | ~v1_funct_1(C_106))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.34  tff(c_197, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_107, c_179])).
% 2.37/1.34  tff(c_206, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_197])).
% 2.37/1.34  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_206])).
% 2.37/1.34  tff(c_209, plain, (~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_84])).
% 2.37/1.34  tff(c_85, plain, (v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_44])).
% 2.37/1.34  tff(c_210, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_84])).
% 2.37/1.34  tff(c_211, plain, (![C_107, A_108, B_109]: (v1_funct_2(C_107, A_108, B_109) | ~v1_partfun1(C_107, A_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_1(C_107))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.37/1.34  tff(c_214, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_210, c_211])).
% 2.37/1.34  tff(c_220, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_partfun1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_214])).
% 2.37/1.34  tff(c_221, plain, (~v1_partfun1('#skF_8', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_209, c_220])).
% 2.37/1.34  tff(c_226, plain, (![B_110, E_111, A_112, C_113]: ('#skF_4'(B_110, E_111, k5_partfun1(A_112, B_110, C_113), C_113, A_112)=E_111 | ~r2_hidden(E_111, k5_partfun1(A_112, B_110, C_113)) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_112, B_110))) | ~v1_funct_1(C_113))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.34  tff(c_228, plain, ('#skF_4'('#skF_6', '#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_7', '#skF_5')='#skF_8' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_46, c_226])).
% 2.37/1.34  tff(c_231, plain, ('#skF_4'('#skF_6', '#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'), '#skF_7', '#skF_5')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_228])).
% 2.37/1.34  tff(c_260, plain, (![B_124, E_125, A_126, C_127]: (v1_partfun1('#skF_4'(B_124, E_125, k5_partfun1(A_126, B_124, C_127), C_127, A_126), A_126) | ~r2_hidden(E_125, k5_partfun1(A_126, B_124, C_127)) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_124))) | ~v1_funct_1(C_127))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.37/1.34  tff(c_263, plain, (v1_partfun1('#skF_8', '#skF_5') | ~r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_231, c_260])).
% 2.37/1.34  tff(c_265, plain, (v1_partfun1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_263])).
% 2.37/1.34  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_265])).
% 2.37/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.34  
% 2.37/1.34  Inference rules
% 2.37/1.34  ----------------------
% 2.37/1.34  #Ref     : 0
% 2.37/1.34  #Sup     : 41
% 2.37/1.34  #Fact    : 0
% 2.37/1.34  #Define  : 0
% 2.37/1.34  #Split   : 5
% 2.37/1.34  #Chain   : 0
% 2.37/1.34  #Close   : 0
% 2.37/1.34  
% 2.37/1.34  Ordering : KBO
% 2.37/1.34  
% 2.37/1.34  Simplification rules
% 2.37/1.34  ----------------------
% 2.37/1.34  #Subsume      : 1
% 2.37/1.34  #Demod        : 39
% 2.37/1.34  #Tautology    : 10
% 2.37/1.34  #SimpNegUnit  : 4
% 2.37/1.34  #BackRed      : 0
% 2.37/1.34  
% 2.37/1.34  #Partial instantiations: 0
% 2.37/1.34  #Strategies tried      : 1
% 2.37/1.34  
% 2.37/1.34  Timing (in seconds)
% 2.37/1.34  ----------------------
% 2.37/1.35  Preprocessing        : 0.33
% 2.37/1.35  Parsing              : 0.16
% 2.37/1.35  CNF conversion       : 0.03
% 2.37/1.35  Main loop            : 0.24
% 2.37/1.35  Inferencing          : 0.09
% 2.37/1.35  Reduction            : 0.07
% 2.37/1.35  Demodulation         : 0.05
% 2.37/1.35  BG Simplification    : 0.02
% 2.37/1.35  Subsumption          : 0.04
% 2.37/1.35  Abstraction          : 0.02
% 2.37/1.35  MUC search           : 0.00
% 2.37/1.35  Cooper               : 0.00
% 2.37/1.35  Total                : 0.61
% 2.37/1.35  Index Insertion      : 0.00
% 2.37/1.35  Index Deletion       : 0.00
% 2.37/1.35  Index Matching       : 0.00
% 2.37/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
