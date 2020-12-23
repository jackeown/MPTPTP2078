%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:59 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 129 expanded)
%              Number of leaves         :   26 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  117 ( 411 expanded)
%              Number of equality atoms :    6 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( k1_relat_1(C) = A
            & ! [D] :
                ( r2_hidden(D,A)
               => r2_hidden(k1_funct_1(C,D),B) ) )
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_261,plain,(
    ! [B_110,A_111] :
      ( m1_subset_1(B_110,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_110),A_111)))
      | ~ r1_tarski(k2_relat_1(B_110),A_111)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_264,plain,(
    ! [A_111] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',A_111)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),A_111)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_261])).

tff(c_267,plain,(
    ! [A_112] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',A_112)))
      | ~ r1_tarski(k2_relat_1('#skF_8'),A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_264])).

tff(c_32,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32])).

tff(c_63,plain,(
    ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_79,C_80] :
      ( r2_hidden('#skF_5'(A_79,k2_relat_1(A_79),C_80),k1_relat_1(A_79))
      | ~ r2_hidden(C_80,k2_relat_1(A_79))
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    ! [C_80] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_80),'#skF_6')
      | ~ r2_hidden(C_80,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_108])).

tff(c_116,plain,(
    ! [C_80] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_80),'#skF_6')
      | ~ r2_hidden(C_80,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_113])).

tff(c_125,plain,(
    ! [A_84,C_85] :
      ( k1_funct_1(A_84,'#skF_5'(A_84,k2_relat_1(A_84),C_85)) = C_85
      | ~ r2_hidden(C_85,k2_relat_1(A_84))
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    ! [D_49] :
      ( r2_hidden(k1_funct_1('#skF_8',D_49),'#skF_7')
      | ~ r2_hidden(D_49,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_139,plain,(
    ! [C_85] :
      ( r2_hidden(C_85,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_85),'#skF_6')
      | ~ r2_hidden(C_85,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_34])).

tff(c_149,plain,(
    ! [C_86] :
      ( r2_hidden(C_86,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_86),'#skF_6')
      | ~ r2_hidden(C_86,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_139])).

tff(c_162,plain,(
    ! [C_89] :
      ( r2_hidden(C_89,'#skF_7')
      | ~ r2_hidden(C_89,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_116,c_149])).

tff(c_190,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_90),'#skF_7')
      | r1_tarski(k2_relat_1('#skF_8'),B_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_162])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_198,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_190,c_4])).

tff(c_77,plain,(
    ! [B_64,A_65] :
      ( v1_funct_2(B_64,k1_relat_1(B_64),A_65)
      | ~ r1_tarski(k2_relat_1(B_64),A_65)
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_80,plain,(
    ! [A_65] :
      ( v1_funct_2('#skF_8','#skF_6',A_65)
      | ~ r1_tarski(k2_relat_1('#skF_8'),A_65)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_77])).

tff(c_82,plain,(
    ! [A_65] :
      ( v1_funct_2('#skF_8','#skF_6',A_65)
      | ~ r1_tarski(k2_relat_1('#skF_8'),A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_80])).

tff(c_215,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_198,c_82])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_215])).

tff(c_222,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_271,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_267,c_222])).

tff(c_296,plain,(
    ! [A_115,C_116] :
      ( r2_hidden('#skF_5'(A_115,k2_relat_1(A_115),C_116),k1_relat_1(A_115))
      | ~ r2_hidden(C_116,k2_relat_1(A_115))
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_301,plain,(
    ! [C_116] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_116),'#skF_6')
      | ~ r2_hidden(C_116,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_296])).

tff(c_304,plain,(
    ! [C_116] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_116),'#skF_6')
      | ~ r2_hidden(C_116,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_301])).

tff(c_272,plain,(
    ! [A_113,C_114] :
      ( k1_funct_1(A_113,'#skF_5'(A_113,k2_relat_1(A_113),C_114)) = C_114
      | ~ r2_hidden(C_114,k2_relat_1(A_113))
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_286,plain,(
    ! [C_114] :
      ( r2_hidden(C_114,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_114),'#skF_6')
      | ~ r2_hidden(C_114,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_34])).

tff(c_309,plain,(
    ! [C_118] :
      ( r2_hidden(C_118,'#skF_7')
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_118),'#skF_6')
      | ~ r2_hidden(C_118,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_286])).

tff(c_314,plain,(
    ! [C_119] :
      ( r2_hidden(C_119,'#skF_7')
      | ~ r2_hidden(C_119,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_304,c_309])).

tff(c_346,plain,(
    ! [B_122] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_122),'#skF_7')
      | r1_tarski(k2_relat_1('#skF_8'),B_122) ) ),
    inference(resolution,[status(thm)],[c_6,c_314])).

tff(c_352,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_346,c_4])).

tff(c_357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_271,c_352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.32  
% 2.07/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.32  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.07/1.32  
% 2.07/1.32  %Foreground sorts:
% 2.07/1.32  
% 2.07/1.32  
% 2.07/1.32  %Background operators:
% 2.07/1.32  
% 2.07/1.32  
% 2.07/1.32  %Foreground operators:
% 2.07/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.07/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.07/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.07/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.07/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.07/1.32  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.07/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.07/1.32  tff('#skF_8', type, '#skF_8': $i).
% 2.07/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.07/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.07/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.32  
% 2.48/1.34  tff(f_77, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 2.48/1.34  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 2.48/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.48/1.34  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.48/1.34  tff(c_40, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.48/1.34  tff(c_38, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.48/1.34  tff(c_36, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.48/1.34  tff(c_261, plain, (![B_110, A_111]: (m1_subset_1(B_110, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_110), A_111))) | ~r1_tarski(k2_relat_1(B_110), A_111) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.48/1.34  tff(c_264, plain, (![A_111]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', A_111))) | ~r1_tarski(k2_relat_1('#skF_8'), A_111) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_261])).
% 2.48/1.34  tff(c_267, plain, (![A_112]: (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', A_112))) | ~r1_tarski(k2_relat_1('#skF_8'), A_112))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_264])).
% 2.48/1.34  tff(c_32, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.48/1.34  tff(c_42, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32])).
% 2.48/1.34  tff(c_63, plain, (~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_42])).
% 2.48/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.48/1.34  tff(c_108, plain, (![A_79, C_80]: (r2_hidden('#skF_5'(A_79, k2_relat_1(A_79), C_80), k1_relat_1(A_79)) | ~r2_hidden(C_80, k2_relat_1(A_79)) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.48/1.34  tff(c_113, plain, (![C_80]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_80), '#skF_6') | ~r2_hidden(C_80, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_108])).
% 2.48/1.34  tff(c_116, plain, (![C_80]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_80), '#skF_6') | ~r2_hidden(C_80, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_113])).
% 2.48/1.34  tff(c_125, plain, (![A_84, C_85]: (k1_funct_1(A_84, '#skF_5'(A_84, k2_relat_1(A_84), C_85))=C_85 | ~r2_hidden(C_85, k2_relat_1(A_84)) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.48/1.34  tff(c_34, plain, (![D_49]: (r2_hidden(k1_funct_1('#skF_8', D_49), '#skF_7') | ~r2_hidden(D_49, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.48/1.34  tff(c_139, plain, (![C_85]: (r2_hidden(C_85, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_85), '#skF_6') | ~r2_hidden(C_85, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_125, c_34])).
% 2.48/1.34  tff(c_149, plain, (![C_86]: (r2_hidden(C_86, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_86), '#skF_6') | ~r2_hidden(C_86, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_139])).
% 2.48/1.34  tff(c_162, plain, (![C_89]: (r2_hidden(C_89, '#skF_7') | ~r2_hidden(C_89, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_116, c_149])).
% 2.48/1.34  tff(c_190, plain, (![B_90]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_90), '#skF_7') | r1_tarski(k2_relat_1('#skF_8'), B_90))), inference(resolution, [status(thm)], [c_6, c_162])).
% 2.48/1.34  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.48/1.34  tff(c_198, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_190, c_4])).
% 2.48/1.34  tff(c_77, plain, (![B_64, A_65]: (v1_funct_2(B_64, k1_relat_1(B_64), A_65) | ~r1_tarski(k2_relat_1(B_64), A_65) | ~v1_funct_1(B_64) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.48/1.34  tff(c_80, plain, (![A_65]: (v1_funct_2('#skF_8', '#skF_6', A_65) | ~r1_tarski(k2_relat_1('#skF_8'), A_65) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_77])).
% 2.48/1.34  tff(c_82, plain, (![A_65]: (v1_funct_2('#skF_8', '#skF_6', A_65) | ~r1_tarski(k2_relat_1('#skF_8'), A_65))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_80])).
% 2.48/1.34  tff(c_215, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_198, c_82])).
% 2.48/1.34  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_215])).
% 2.48/1.34  tff(c_222, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(splitRight, [status(thm)], [c_42])).
% 2.48/1.34  tff(c_271, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_267, c_222])).
% 2.48/1.34  tff(c_296, plain, (![A_115, C_116]: (r2_hidden('#skF_5'(A_115, k2_relat_1(A_115), C_116), k1_relat_1(A_115)) | ~r2_hidden(C_116, k2_relat_1(A_115)) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.48/1.34  tff(c_301, plain, (![C_116]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_116), '#skF_6') | ~r2_hidden(C_116, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_296])).
% 2.48/1.34  tff(c_304, plain, (![C_116]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_116), '#skF_6') | ~r2_hidden(C_116, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_301])).
% 2.48/1.34  tff(c_272, plain, (![A_113, C_114]: (k1_funct_1(A_113, '#skF_5'(A_113, k2_relat_1(A_113), C_114))=C_114 | ~r2_hidden(C_114, k2_relat_1(A_113)) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.48/1.34  tff(c_286, plain, (![C_114]: (r2_hidden(C_114, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_114), '#skF_6') | ~r2_hidden(C_114, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_272, c_34])).
% 2.48/1.34  tff(c_309, plain, (![C_118]: (r2_hidden(C_118, '#skF_7') | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_118), '#skF_6') | ~r2_hidden(C_118, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_286])).
% 2.48/1.34  tff(c_314, plain, (![C_119]: (r2_hidden(C_119, '#skF_7') | ~r2_hidden(C_119, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_304, c_309])).
% 2.48/1.34  tff(c_346, plain, (![B_122]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_122), '#skF_7') | r1_tarski(k2_relat_1('#skF_8'), B_122))), inference(resolution, [status(thm)], [c_6, c_314])).
% 2.48/1.34  tff(c_352, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_346, c_4])).
% 2.48/1.34  tff(c_357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_271, c_271, c_352])).
% 2.48/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.34  
% 2.48/1.34  Inference rules
% 2.48/1.34  ----------------------
% 2.48/1.34  #Ref     : 0
% 2.48/1.34  #Sup     : 64
% 2.48/1.34  #Fact    : 0
% 2.48/1.34  #Define  : 0
% 2.48/1.34  #Split   : 1
% 2.48/1.34  #Chain   : 0
% 2.48/1.34  #Close   : 0
% 2.48/1.34  
% 2.48/1.34  Ordering : KBO
% 2.48/1.34  
% 2.48/1.34  Simplification rules
% 2.48/1.34  ----------------------
% 2.48/1.34  #Subsume      : 12
% 2.48/1.34  #Demod        : 29
% 2.48/1.34  #Tautology    : 11
% 2.48/1.34  #SimpNegUnit  : 2
% 2.48/1.34  #BackRed      : 0
% 2.48/1.34  
% 2.48/1.34  #Partial instantiations: 0
% 2.48/1.34  #Strategies tried      : 1
% 2.48/1.34  
% 2.48/1.34  Timing (in seconds)
% 2.48/1.34  ----------------------
% 2.48/1.34  Preprocessing        : 0.30
% 2.48/1.34  Parsing              : 0.16
% 2.48/1.34  CNF conversion       : 0.03
% 2.48/1.34  Main loop            : 0.26
% 2.48/1.34  Inferencing          : 0.10
% 2.48/1.34  Reduction            : 0.07
% 2.48/1.34  Demodulation         : 0.05
% 2.48/1.34  BG Simplification    : 0.02
% 2.48/1.34  Subsumption          : 0.05
% 2.48/1.34  Abstraction          : 0.01
% 2.48/1.34  MUC search           : 0.00
% 2.48/1.34  Cooper               : 0.00
% 2.48/1.34  Total                : 0.60
% 2.48/1.34  Index Insertion      : 0.00
% 2.48/1.34  Index Deletion       : 0.00
% 2.48/1.34  Index Matching       : 0.00
% 2.48/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
