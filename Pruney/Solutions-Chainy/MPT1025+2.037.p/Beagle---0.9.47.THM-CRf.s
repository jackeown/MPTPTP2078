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
% DateTime   : Thu Dec  3 10:16:35 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 124 expanded)
%              Number of leaves         :   36 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  149 ( 297 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1

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
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_68,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_68])).

tff(c_74,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_71])).

tff(c_56,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [A_78,B_79] :
      ( ~ r2_hidden('#skF_1'(A_78,B_79),B_79)
      | r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_95,plain,(
    ! [B_85,A_86] :
      ( v4_relat_1(B_85,A_86)
      | ~ r1_tarski(k1_relat_1(B_85),A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_104,plain,(
    ! [B_85] :
      ( v4_relat_1(B_85,k1_relat_1(B_85))
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_86,c_95])).

tff(c_113,plain,(
    ! [C_91,A_92,B_93] :
      ( v4_relat_1(C_91,A_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_122,plain,(
    v4_relat_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_113])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_106,plain,(
    ! [C_88,B_89,A_90] :
      ( r2_hidden(C_88,B_89)
      | ~ r2_hidden(C_88,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_98,B_99,B_100] :
      ( r2_hidden('#skF_1'(A_98,B_99),B_100)
      | ~ r1_tarski(A_98,B_100)
      | r1_tarski(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_239,plain,(
    ! [A_122,B_123,B_124,B_125] :
      ( r2_hidden('#skF_1'(A_122,B_123),B_124)
      | ~ r1_tarski(B_125,B_124)
      | ~ r1_tarski(A_122,B_125)
      | r1_tarski(A_122,B_123) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_291,plain,(
    ! [A_144,B_145,A_146,B_147] :
      ( r2_hidden('#skF_1'(A_144,B_145),A_146)
      | ~ r1_tarski(A_144,k1_relat_1(B_147))
      | r1_tarski(A_144,B_145)
      | ~ v4_relat_1(B_147,A_146)
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_14,c_239])).

tff(c_731,plain,(
    ! [B_248,B_249,A_250,B_251] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_248),B_249),A_250)
      | r1_tarski(k1_relat_1(B_248),B_249)
      | ~ v4_relat_1(B_251,A_250)
      | ~ v1_relat_1(B_251)
      | ~ v4_relat_1(B_248,k1_relat_1(B_251))
      | ~ v1_relat_1(B_248) ) ),
    inference(resolution,[status(thm)],[c_14,c_291])).

tff(c_735,plain,(
    ! [B_248,B_249] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_248),B_249),'#skF_6')
      | r1_tarski(k1_relat_1(B_248),B_249)
      | ~ v1_relat_1('#skF_9')
      | ~ v4_relat_1(B_248,k1_relat_1('#skF_9'))
      | ~ v1_relat_1(B_248) ) ),
    inference(resolution,[status(thm)],[c_122,c_731])).

tff(c_743,plain,(
    ! [B_252,B_253] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_252),B_253),'#skF_6')
      | r1_tarski(k1_relat_1(B_252),B_253)
      | ~ v4_relat_1(B_252,k1_relat_1('#skF_9'))
      | ~ v1_relat_1(B_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_735])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_756,plain,(
    ! [B_254] :
      ( r1_tarski(k1_relat_1(B_254),'#skF_6')
      | ~ v4_relat_1(B_254,k1_relat_1('#skF_9'))
      | ~ v1_relat_1(B_254) ) ),
    inference(resolution,[status(thm)],[c_743,c_4])).

tff(c_764,plain,
    ( r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_104,c_756])).

tff(c_768,plain,(
    r1_tarski(k1_relat_1('#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_764])).

tff(c_20,plain,(
    ! [A_15,B_38,D_53] :
      ( k1_funct_1(A_15,'#skF_5'(A_15,B_38,k9_relat_1(A_15,B_38),D_53)) = D_53
      | ~ r2_hidden(D_53,k9_relat_1(A_15,B_38))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_413,plain,(
    ! [A_182,B_183,D_184] :
      ( r2_hidden('#skF_5'(A_182,B_183,k9_relat_1(A_182,B_183),D_184),k1_relat_1(A_182))
      | ~ r2_hidden(D_184,k9_relat_1(A_182,B_183))
      | ~ v1_funct_1(A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1182,plain,(
    ! [A_332,B_333,D_334,B_335] :
      ( r2_hidden('#skF_5'(A_332,B_333,k9_relat_1(A_332,B_333),D_334),B_335)
      | ~ r1_tarski(k1_relat_1(A_332),B_335)
      | ~ r2_hidden(D_334,k9_relat_1(A_332,B_333))
      | ~ v1_funct_1(A_332)
      | ~ v1_relat_1(A_332) ) ),
    inference(resolution,[status(thm)],[c_413,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1208,plain,(
    ! [A_346,B_347,D_348,B_349] :
      ( m1_subset_1('#skF_5'(A_346,B_347,k9_relat_1(A_346,B_347),D_348),B_349)
      | ~ r1_tarski(k1_relat_1(A_346),B_349)
      | ~ r2_hidden(D_348,k9_relat_1(A_346,B_347))
      | ~ v1_funct_1(A_346)
      | ~ v1_relat_1(A_346) ) ),
    inference(resolution,[status(thm)],[c_1182,c_8])).

tff(c_277,plain,(
    ! [A_139,B_140,D_141] :
      ( r2_hidden('#skF_5'(A_139,B_140,k9_relat_1(A_139,B_140),D_141),B_140)
      | ~ r2_hidden(D_141,k9_relat_1(A_139,B_140))
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    ! [F_68] :
      ( k1_funct_1('#skF_9',F_68) != '#skF_10'
      | ~ r2_hidden(F_68,'#skF_8')
      | ~ m1_subset_1(F_68,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_288,plain,(
    ! [A_139,D_141] :
      ( k1_funct_1('#skF_9','#skF_5'(A_139,'#skF_8',k9_relat_1(A_139,'#skF_8'),D_141)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'(A_139,'#skF_8',k9_relat_1(A_139,'#skF_8'),D_141),'#skF_6')
      | ~ r2_hidden(D_141,k9_relat_1(A_139,'#skF_8'))
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(resolution,[status(thm)],[c_277,c_48])).

tff(c_1503,plain,(
    ! [A_398,D_399] :
      ( k1_funct_1('#skF_9','#skF_5'(A_398,'#skF_8',k9_relat_1(A_398,'#skF_8'),D_399)) != '#skF_10'
      | ~ r1_tarski(k1_relat_1(A_398),'#skF_6')
      | ~ r2_hidden(D_399,k9_relat_1(A_398,'#skF_8'))
      | ~ v1_funct_1(A_398)
      | ~ v1_relat_1(A_398) ) ),
    inference(resolution,[status(thm)],[c_1208,c_288])).

tff(c_1507,plain,(
    ! [D_53] :
      ( D_53 != '#skF_10'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
      | ~ r2_hidden(D_53,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_53,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1503])).

tff(c_1510,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_56,c_74,c_56,c_768,c_1507])).

tff(c_159,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( k7_relset_1(A_103,B_104,C_105,D_106) = k9_relat_1(C_105,D_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_166,plain,(
    ! [D_106] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_106) = k9_relat_1('#skF_9',D_106) ),
    inference(resolution,[status(thm)],[c_52,c_159])).

tff(c_50,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_169,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_50])).

tff(c_1512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1510,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.81  
% 4.62/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.81  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 4.62/1.81  
% 4.62/1.81  %Foreground sorts:
% 4.62/1.81  
% 4.62/1.81  
% 4.62/1.81  %Background operators:
% 4.62/1.81  
% 4.62/1.81  
% 4.62/1.81  %Foreground operators:
% 4.62/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.62/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.62/1.81  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.62/1.81  tff('#skF_7', type, '#skF_7': $i).
% 4.62/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.81  tff('#skF_10', type, '#skF_10': $i).
% 4.62/1.81  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.62/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.62/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.62/1.81  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.62/1.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.62/1.81  tff('#skF_9', type, '#skF_9': $i).
% 4.62/1.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.62/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.81  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.62/1.81  tff('#skF_8', type, '#skF_8': $i).
% 4.62/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.81  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.62/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.62/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.62/1.81  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.62/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.62/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.62/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.62/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/1.81  
% 4.62/1.82  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.62/1.82  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 4.62/1.82  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.62/1.82  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.62/1.82  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.62/1.82  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.62/1.82  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 4.62/1.82  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.62/1.82  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.62/1.82  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.62/1.82  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.62/1.82  tff(c_68, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.62/1.82  tff(c_71, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_52, c_68])).
% 4.62/1.82  tff(c_74, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_71])).
% 4.62/1.82  tff(c_56, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.62/1.82  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.62/1.82  tff(c_81, plain, (![A_78, B_79]: (~r2_hidden('#skF_1'(A_78, B_79), B_79) | r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.62/1.82  tff(c_86, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_81])).
% 4.62/1.82  tff(c_95, plain, (![B_85, A_86]: (v4_relat_1(B_85, A_86) | ~r1_tarski(k1_relat_1(B_85), A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.62/1.82  tff(c_104, plain, (![B_85]: (v4_relat_1(B_85, k1_relat_1(B_85)) | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_86, c_95])).
% 4.62/1.82  tff(c_113, plain, (![C_91, A_92, B_93]: (v4_relat_1(C_91, A_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.62/1.82  tff(c_122, plain, (v4_relat_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_113])).
% 4.62/1.82  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.62/1.82  tff(c_106, plain, (![C_88, B_89, A_90]: (r2_hidden(C_88, B_89) | ~r2_hidden(C_88, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.62/1.82  tff(c_140, plain, (![A_98, B_99, B_100]: (r2_hidden('#skF_1'(A_98, B_99), B_100) | ~r1_tarski(A_98, B_100) | r1_tarski(A_98, B_99))), inference(resolution, [status(thm)], [c_6, c_106])).
% 4.62/1.82  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.62/1.82  tff(c_239, plain, (![A_122, B_123, B_124, B_125]: (r2_hidden('#skF_1'(A_122, B_123), B_124) | ~r1_tarski(B_125, B_124) | ~r1_tarski(A_122, B_125) | r1_tarski(A_122, B_123))), inference(resolution, [status(thm)], [c_140, c_2])).
% 4.62/1.82  tff(c_291, plain, (![A_144, B_145, A_146, B_147]: (r2_hidden('#skF_1'(A_144, B_145), A_146) | ~r1_tarski(A_144, k1_relat_1(B_147)) | r1_tarski(A_144, B_145) | ~v4_relat_1(B_147, A_146) | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_14, c_239])).
% 4.62/1.82  tff(c_731, plain, (![B_248, B_249, A_250, B_251]: (r2_hidden('#skF_1'(k1_relat_1(B_248), B_249), A_250) | r1_tarski(k1_relat_1(B_248), B_249) | ~v4_relat_1(B_251, A_250) | ~v1_relat_1(B_251) | ~v4_relat_1(B_248, k1_relat_1(B_251)) | ~v1_relat_1(B_248))), inference(resolution, [status(thm)], [c_14, c_291])).
% 4.62/1.82  tff(c_735, plain, (![B_248, B_249]: (r2_hidden('#skF_1'(k1_relat_1(B_248), B_249), '#skF_6') | r1_tarski(k1_relat_1(B_248), B_249) | ~v1_relat_1('#skF_9') | ~v4_relat_1(B_248, k1_relat_1('#skF_9')) | ~v1_relat_1(B_248))), inference(resolution, [status(thm)], [c_122, c_731])).
% 4.62/1.82  tff(c_743, plain, (![B_252, B_253]: (r2_hidden('#skF_1'(k1_relat_1(B_252), B_253), '#skF_6') | r1_tarski(k1_relat_1(B_252), B_253) | ~v4_relat_1(B_252, k1_relat_1('#skF_9')) | ~v1_relat_1(B_252))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_735])).
% 4.62/1.82  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.62/1.82  tff(c_756, plain, (![B_254]: (r1_tarski(k1_relat_1(B_254), '#skF_6') | ~v4_relat_1(B_254, k1_relat_1('#skF_9')) | ~v1_relat_1(B_254))), inference(resolution, [status(thm)], [c_743, c_4])).
% 4.62/1.82  tff(c_764, plain, (r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_104, c_756])).
% 4.62/1.82  tff(c_768, plain, (r1_tarski(k1_relat_1('#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_764])).
% 4.62/1.82  tff(c_20, plain, (![A_15, B_38, D_53]: (k1_funct_1(A_15, '#skF_5'(A_15, B_38, k9_relat_1(A_15, B_38), D_53))=D_53 | ~r2_hidden(D_53, k9_relat_1(A_15, B_38)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.62/1.82  tff(c_413, plain, (![A_182, B_183, D_184]: (r2_hidden('#skF_5'(A_182, B_183, k9_relat_1(A_182, B_183), D_184), k1_relat_1(A_182)) | ~r2_hidden(D_184, k9_relat_1(A_182, B_183)) | ~v1_funct_1(A_182) | ~v1_relat_1(A_182))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.62/1.82  tff(c_1182, plain, (![A_332, B_333, D_334, B_335]: (r2_hidden('#skF_5'(A_332, B_333, k9_relat_1(A_332, B_333), D_334), B_335) | ~r1_tarski(k1_relat_1(A_332), B_335) | ~r2_hidden(D_334, k9_relat_1(A_332, B_333)) | ~v1_funct_1(A_332) | ~v1_relat_1(A_332))), inference(resolution, [status(thm)], [c_413, c_2])).
% 4.62/1.82  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.62/1.82  tff(c_1208, plain, (![A_346, B_347, D_348, B_349]: (m1_subset_1('#skF_5'(A_346, B_347, k9_relat_1(A_346, B_347), D_348), B_349) | ~r1_tarski(k1_relat_1(A_346), B_349) | ~r2_hidden(D_348, k9_relat_1(A_346, B_347)) | ~v1_funct_1(A_346) | ~v1_relat_1(A_346))), inference(resolution, [status(thm)], [c_1182, c_8])).
% 4.62/1.82  tff(c_277, plain, (![A_139, B_140, D_141]: (r2_hidden('#skF_5'(A_139, B_140, k9_relat_1(A_139, B_140), D_141), B_140) | ~r2_hidden(D_141, k9_relat_1(A_139, B_140)) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.62/1.82  tff(c_48, plain, (![F_68]: (k1_funct_1('#skF_9', F_68)!='#skF_10' | ~r2_hidden(F_68, '#skF_8') | ~m1_subset_1(F_68, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.62/1.82  tff(c_288, plain, (![A_139, D_141]: (k1_funct_1('#skF_9', '#skF_5'(A_139, '#skF_8', k9_relat_1(A_139, '#skF_8'), D_141))!='#skF_10' | ~m1_subset_1('#skF_5'(A_139, '#skF_8', k9_relat_1(A_139, '#skF_8'), D_141), '#skF_6') | ~r2_hidden(D_141, k9_relat_1(A_139, '#skF_8')) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(resolution, [status(thm)], [c_277, c_48])).
% 4.62/1.82  tff(c_1503, plain, (![A_398, D_399]: (k1_funct_1('#skF_9', '#skF_5'(A_398, '#skF_8', k9_relat_1(A_398, '#skF_8'), D_399))!='#skF_10' | ~r1_tarski(k1_relat_1(A_398), '#skF_6') | ~r2_hidden(D_399, k9_relat_1(A_398, '#skF_8')) | ~v1_funct_1(A_398) | ~v1_relat_1(A_398))), inference(resolution, [status(thm)], [c_1208, c_288])).
% 4.62/1.82  tff(c_1507, plain, (![D_53]: (D_53!='#skF_10' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~r2_hidden(D_53, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_53, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1503])).
% 4.62/1.82  tff(c_1510, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_56, c_74, c_56, c_768, c_1507])).
% 4.62/1.82  tff(c_159, plain, (![A_103, B_104, C_105, D_106]: (k7_relset_1(A_103, B_104, C_105, D_106)=k9_relat_1(C_105, D_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.62/1.82  tff(c_166, plain, (![D_106]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_106)=k9_relat_1('#skF_9', D_106))), inference(resolution, [status(thm)], [c_52, c_159])).
% 4.62/1.82  tff(c_50, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.62/1.82  tff(c_169, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_50])).
% 4.62/1.82  tff(c_1512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1510, c_169])).
% 4.62/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.82  
% 4.62/1.82  Inference rules
% 4.62/1.82  ----------------------
% 4.62/1.82  #Ref     : 0
% 4.62/1.82  #Sup     : 307
% 4.62/1.82  #Fact    : 0
% 4.62/1.82  #Define  : 0
% 4.62/1.82  #Split   : 6
% 4.62/1.82  #Chain   : 0
% 4.62/1.82  #Close   : 0
% 4.62/1.82  
% 4.62/1.82  Ordering : KBO
% 4.62/1.82  
% 4.62/1.82  Simplification rules
% 4.62/1.82  ----------------------
% 4.62/1.82  #Subsume      : 60
% 4.62/1.82  #Demod        : 42
% 4.62/1.82  #Tautology    : 19
% 4.62/1.82  #SimpNegUnit  : 1
% 4.62/1.82  #BackRed      : 4
% 4.62/1.82  
% 4.62/1.82  #Partial instantiations: 0
% 4.62/1.82  #Strategies tried      : 1
% 4.62/1.82  
% 4.62/1.82  Timing (in seconds)
% 4.62/1.82  ----------------------
% 4.62/1.83  Preprocessing        : 0.35
% 4.62/1.83  Parsing              : 0.17
% 4.62/1.83  CNF conversion       : 0.03
% 4.62/1.83  Main loop            : 0.72
% 4.62/1.83  Inferencing          : 0.30
% 4.62/1.83  Reduction            : 0.17
% 4.62/1.83  Demodulation         : 0.12
% 4.62/1.83  BG Simplification    : 0.03
% 4.62/1.83  Subsumption          : 0.16
% 4.62/1.83  Abstraction          : 0.04
% 4.62/1.83  MUC search           : 0.00
% 4.62/1.83  Cooper               : 0.00
% 4.62/1.83  Total                : 1.10
% 4.62/1.83  Index Insertion      : 0.00
% 4.62/1.83  Index Deletion       : 0.00
% 4.62/1.83  Index Matching       : 0.00
% 4.62/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
