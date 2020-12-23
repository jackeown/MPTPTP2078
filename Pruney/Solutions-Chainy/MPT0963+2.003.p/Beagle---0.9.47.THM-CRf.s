%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:58 EST 2020

% Result     : Theorem 42.19s
% Output     : CNFRefutation 42.41s
% Verified   : 
% Statistics : Number of formulae       :  288 (2412 expanded)
%              Number of leaves         :   35 ( 900 expanded)
%              Depth                    :   27
%              Number of atoms          :  973 (10738 expanded)
%              Number of equality atoms :  146 (1676 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_13 > #skF_5 > #skF_2 > #skF_8 > #skF_4 > #skF_3 > #skF_7 > #skF_9 > #skF_12 > #skF_10

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_71,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_42,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(c_78,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_76,plain,(
    v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_74,plain,(
    k1_relat_1('#skF_13') = '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_94019,plain,(
    ! [A_3288,C_3289] :
      ( r2_hidden('#skF_10'(A_3288,k2_relat_1(A_3288),C_3289),k1_relat_1(A_3288))
      | ~ r2_hidden(C_3289,k2_relat_1(A_3288))
      | ~ v1_funct_1(A_3288)
      | ~ v1_relat_1(A_3288) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_94022,plain,(
    ! [C_3289] :
      ( r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),C_3289),'#skF_11')
      | ~ r2_hidden(C_3289,k2_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_94019])).

tff(c_94024,plain,(
    ! [C_3289] :
      ( r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),C_3289),'#skF_11')
      | ~ r2_hidden(C_3289,k2_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_94022])).

tff(c_46,plain,(
    ! [A_55,C_91] :
      ( k1_funct_1(A_55,'#skF_10'(A_55,k2_relat_1(A_55),C_91)) = C_91
      | ~ r2_hidden(C_91,k2_relat_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93986,plain,(
    ! [B_3282,A_3283] :
      ( m1_subset_1(B_3282,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_3282),A_3283)))
      | ~ r1_tarski(k2_relat_1(B_3282),A_3283)
      | ~ v1_funct_1(B_3282)
      | ~ v1_relat_1(B_3282) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_93989,plain,(
    ! [A_3283] :
      ( m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11',A_3283)))
      | ~ r1_tarski(k2_relat_1('#skF_13'),A_3283)
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_93986])).

tff(c_93992,plain,(
    ! [A_3284] :
      ( m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11',A_3284)))
      | ~ r1_tarski(k2_relat_1('#skF_13'),A_3284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_93989])).

tff(c_131,plain,(
    ! [A_120,C_121] :
      ( r2_hidden('#skF_10'(A_120,k2_relat_1(A_120),C_121),k1_relat_1(A_120))
      | ~ r2_hidden(C_121,k2_relat_1(A_120))
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_134,plain,(
    ! [C_121] :
      ( r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),C_121),'#skF_11')
      | ~ r2_hidden(C_121,k2_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_131])).

tff(c_136,plain,(
    ! [C_121] :
      ( r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),C_121),'#skF_11')
      | ~ r2_hidden(C_121,k2_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_134])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12')))
    | ~ v1_funct_2('#skF_13','#skF_11','#skF_12')
    | ~ v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12')))
    | ~ v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70])).

tff(c_86,plain,(
    ~ v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_244,plain,(
    ! [A_141,B_142] :
      ( r2_hidden('#skF_8'(A_141,B_142),k1_relat_1(A_141))
      | r2_hidden('#skF_9'(A_141,B_142),B_142)
      | k2_relat_1(A_141) = B_142
      | ~ v1_funct_1(A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_257,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_8'('#skF_13',B_142),'#skF_11')
      | r2_hidden('#skF_9'('#skF_13',B_142),B_142)
      | k2_relat_1('#skF_13') = B_142
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_244])).

tff(c_261,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_8'('#skF_13',B_142),'#skF_11')
      | r2_hidden('#skF_9'('#skF_13',B_142),B_142)
      | k2_relat_1('#skF_13') = B_142 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_257])).

tff(c_6,plain,(
    ! [A_1,B_24,D_39] :
      ( r2_hidden('#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39),B_24)
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_309,plain,(
    ! [A_149,B_150,D_151] :
      ( k1_funct_1(A_149,'#skF_4'(A_149,B_150,k9_relat_1(A_149,B_150),D_151)) = D_151
      | ~ r2_hidden(D_151,k9_relat_1(A_149,B_150))
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_72,plain,(
    ! [D_100] :
      ( r2_hidden(k1_funct_1('#skF_13',D_100),'#skF_12')
      | ~ r2_hidden(D_100,'#skF_11') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_328,plain,(
    ! [D_151,B_150] :
      ( r2_hidden(D_151,'#skF_12')
      | ~ r2_hidden('#skF_4'('#skF_13',B_150,k9_relat_1('#skF_13',B_150),D_151),'#skF_11')
      | ~ r2_hidden(D_151,k9_relat_1('#skF_13',B_150))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_72])).

tff(c_336,plain,(
    ! [D_152,B_153] :
      ( r2_hidden(D_152,'#skF_12')
      | ~ r2_hidden('#skF_4'('#skF_13',B_153,k9_relat_1('#skF_13',B_153),D_152),'#skF_11')
      | ~ r2_hidden(D_152,k9_relat_1('#skF_13',B_153)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_328])).

tff(c_340,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,'#skF_12')
      | ~ r2_hidden(D_39,k9_relat_1('#skF_13','#skF_11'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_6,c_336])).

tff(c_344,plain,(
    ! [D_154] :
      ( r2_hidden(D_154,'#skF_12')
      | ~ r2_hidden(D_154,k9_relat_1('#skF_13','#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_340])).

tff(c_363,plain,
    ( r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_12')
    | r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11')
    | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_261,c_344])).

tff(c_500,plain,(
    k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13') ),
    inference(splitLeft,[status(thm)],[c_363])).

tff(c_890,plain,(
    ! [A_192,B_193,C_194] :
      ( r2_hidden('#skF_5'(A_192,B_193,C_194),k1_relat_1(A_192))
      | r2_hidden('#skF_6'(A_192,B_193,C_194),C_194)
      | k10_relat_1(A_192,B_193) = C_194
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_920,plain,(
    ! [B_193,C_194] :
      ( r2_hidden('#skF_5'('#skF_13',B_193,C_194),'#skF_11')
      | r2_hidden('#skF_6'('#skF_13',B_193,C_194),C_194)
      | k10_relat_1('#skF_13',B_193) = C_194
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_890])).

tff(c_929,plain,(
    ! [B_193,C_194] :
      ( r2_hidden('#skF_5'('#skF_13',B_193,C_194),'#skF_11')
      | r2_hidden('#skF_6'('#skF_13',B_193,C_194),C_194)
      | k10_relat_1('#skF_13',B_193) = C_194 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_920])).

tff(c_3188,plain,(
    ! [A_362,B_363,C_364] :
      ( r2_hidden('#skF_5'(A_362,B_363,C_364),k1_relat_1(A_362))
      | ~ r2_hidden(k1_funct_1(A_362,'#skF_6'(A_362,B_363,C_364)),B_363)
      | ~ r2_hidden('#skF_6'(A_362,B_363,C_364),k1_relat_1(A_362))
      | k10_relat_1(A_362,B_363) = C_364
      | ~ v1_funct_1(A_362)
      | ~ v1_relat_1(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3252,plain,(
    ! [C_364] :
      ( r2_hidden('#skF_5'('#skF_13','#skF_12',C_364),k1_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_6'('#skF_13','#skF_12',C_364),k1_relat_1('#skF_13'))
      | k10_relat_1('#skF_13','#skF_12') = C_364
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden('#skF_6'('#skF_13','#skF_12',C_364),'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_72,c_3188])).

tff(c_3273,plain,(
    ! [C_365] :
      ( r2_hidden('#skF_5'('#skF_13','#skF_12',C_365),'#skF_11')
      | k10_relat_1('#skF_13','#skF_12') = C_365
      | ~ r2_hidden('#skF_6'('#skF_13','#skF_12',C_365),'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_74,c_3252])).

tff(c_3291,plain,
    ( r2_hidden('#skF_5'('#skF_13','#skF_12','#skF_11'),'#skF_11')
    | k10_relat_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_929,c_3273])).

tff(c_3295,plain,(
    k10_relat_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_3291])).

tff(c_62,plain,(
    ! [B_96,A_95] :
      ( r1_tarski(k9_relat_1(B_96,k10_relat_1(B_96,A_95)),A_95)
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3356,plain,
    ( r1_tarski(k9_relat_1('#skF_13','#skF_11'),'#skF_12')
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_3295,c_62])).

tff(c_3382,plain,(
    r1_tarski(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_500,c_3356])).

tff(c_89,plain,(
    ! [B_107,A_108] :
      ( v1_funct_2(B_107,k1_relat_1(B_107),A_108)
      | ~ r1_tarski(k2_relat_1(B_107),A_108)
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_92,plain,(
    ! [A_108] :
      ( v1_funct_2('#skF_13','#skF_11',A_108)
      | ~ r1_tarski(k2_relat_1('#skF_13'),A_108)
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_89])).

tff(c_94,plain,(
    ! [A_108] :
      ( v1_funct_2('#skF_13','#skF_11',A_108)
      | ~ r1_tarski(k2_relat_1('#skF_13'),A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_92])).

tff(c_3412,plain,(
    v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_3382,c_94])).

tff(c_3416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3412])).

tff(c_3418,plain,(
    k10_relat_1('#skF_13','#skF_12') != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_3291])).

tff(c_3417,plain,(
    r2_hidden('#skF_5'('#skF_13','#skF_12','#skF_11'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_3291])).

tff(c_38,plain,(
    ! [A_43,B_50,C_51] :
      ( ~ r2_hidden('#skF_5'(A_43,B_50,C_51),C_51)
      | r2_hidden('#skF_6'(A_43,B_50,C_51),C_51)
      | k10_relat_1(A_43,B_50) = C_51
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [A_43,B_50,C_51] :
      ( ~ r2_hidden('#skF_5'(A_43,B_50,C_51),C_51)
      | ~ r2_hidden(k1_funct_1(A_43,'#skF_6'(A_43,B_50,C_51)),B_50)
      | ~ r2_hidden('#skF_6'(A_43,B_50,C_51),k1_relat_1(A_43))
      | k10_relat_1(A_43,B_50) = C_51
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3420,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_13','#skF_6'('#skF_13','#skF_12','#skF_11')),'#skF_12')
    | ~ r2_hidden('#skF_6'('#skF_13','#skF_12','#skF_11'),k1_relat_1('#skF_13'))
    | k10_relat_1('#skF_13','#skF_12') = '#skF_11'
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_3417,c_32])).

tff(c_3423,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_13','#skF_6'('#skF_13','#skF_12','#skF_11')),'#skF_12')
    | ~ r2_hidden('#skF_6'('#skF_13','#skF_12','#skF_11'),'#skF_11')
    | k10_relat_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_3420])).

tff(c_3424,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_13','#skF_6'('#skF_13','#skF_12','#skF_11')),'#skF_12')
    | ~ r2_hidden('#skF_6'('#skF_13','#skF_12','#skF_11'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_3418,c_3423])).

tff(c_3425,plain,(
    ~ r2_hidden('#skF_6'('#skF_13','#skF_12','#skF_11'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_3424])).

tff(c_3433,plain,
    ( ~ r2_hidden('#skF_5'('#skF_13','#skF_12','#skF_11'),'#skF_11')
    | k10_relat_1('#skF_13','#skF_12') = '#skF_11'
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_38,c_3425])).

tff(c_3439,plain,(
    k10_relat_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_3417,c_3433])).

tff(c_3441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3418,c_3439])).

tff(c_3443,plain,(
    r2_hidden('#skF_6'('#skF_13','#skF_12','#skF_11'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_3424])).

tff(c_3442,plain,(
    ~ r2_hidden(k1_funct_1('#skF_13','#skF_6'('#skF_13','#skF_12','#skF_11')),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_3424])).

tff(c_3540,plain,(
    ~ r2_hidden('#skF_6'('#skF_13','#skF_12','#skF_11'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_72,c_3442])).

tff(c_3547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3443,c_3540])).

tff(c_3549,plain,(
    k9_relat_1('#skF_13','#skF_11') != k2_relat_1('#skF_13') ),
    inference(splitRight,[status(thm)],[c_363])).

tff(c_44,plain,(
    ! [A_55,D_94] :
      ( r2_hidden(k1_funct_1(A_55,D_94),k2_relat_1(A_55))
      | ~ r2_hidden(D_94,k1_relat_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_220,plain,(
    ! [A_135,E_136,B_137] :
      ( r2_hidden(k1_funct_1(A_135,E_136),k9_relat_1(A_135,B_137))
      | ~ r2_hidden(E_136,B_137)
      | ~ r2_hidden(E_136,k1_relat_1(A_135))
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [D_54,A_43,B_50] :
      ( r2_hidden(D_54,k10_relat_1(A_43,B_50))
      | ~ r2_hidden(k1_funct_1(A_43,D_54),B_50)
      | ~ r2_hidden(D_54,k1_relat_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_227,plain,(
    ! [E_136,A_135,B_137] :
      ( r2_hidden(E_136,k10_relat_1(A_135,k9_relat_1(A_135,B_137)))
      | ~ r2_hidden(E_136,B_137)
      | ~ r2_hidden(E_136,k1_relat_1(A_135))
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(resolution,[status(thm)],[c_220,c_26])).

tff(c_110,plain,(
    ! [A_118,C_119] :
      ( k1_funct_1(A_118,'#skF_10'(A_118,k2_relat_1(A_118),C_119)) = C_119
      | ~ r2_hidden(C_119,k2_relat_1(A_118))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [A_43,D_54,B_50] :
      ( r2_hidden(k1_funct_1(A_43,D_54),B_50)
      | ~ r2_hidden(D_54,k10_relat_1(A_43,B_50))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4133,plain,(
    ! [C_423,B_424,A_425] :
      ( r2_hidden(C_423,B_424)
      | ~ r2_hidden('#skF_10'(A_425,k2_relat_1(A_425),C_423),k10_relat_1(A_425,B_424))
      | ~ v1_funct_1(A_425)
      | ~ v1_relat_1(A_425)
      | ~ r2_hidden(C_423,k2_relat_1(A_425))
      | ~ v1_funct_1(A_425)
      | ~ v1_relat_1(A_425) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_28])).

tff(c_8684,plain,(
    ! [C_704,A_705,B_706] :
      ( r2_hidden(C_704,k9_relat_1(A_705,B_706))
      | ~ r2_hidden(C_704,k2_relat_1(A_705))
      | ~ r2_hidden('#skF_10'(A_705,k2_relat_1(A_705),C_704),B_706)
      | ~ r2_hidden('#skF_10'(A_705,k2_relat_1(A_705),C_704),k1_relat_1(A_705))
      | ~ v1_funct_1(A_705)
      | ~ v1_relat_1(A_705) ) ),
    inference(resolution,[status(thm)],[c_227,c_4133])).

tff(c_8697,plain,(
    ! [C_121] :
      ( r2_hidden(C_121,k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),C_121),k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden(C_121,k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_136,c_8684])).

tff(c_8710,plain,(
    ! [C_707] :
      ( r2_hidden(C_707,k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),C_707),'#skF_11')
      | ~ r2_hidden(C_707,k2_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_8697])).

tff(c_8715,plain,(
    ! [C_708] :
      ( r2_hidden(C_708,k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden(C_708,k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_136,c_8710])).

tff(c_8771,plain,(
    ! [D_709,A_710] :
      ( r2_hidden(D_709,k10_relat_1(A_710,k9_relat_1('#skF_13','#skF_11')))
      | ~ r2_hidden(D_709,k1_relat_1(A_710))
      | ~ v1_funct_1(A_710)
      | ~ v1_relat_1(A_710)
      | ~ r2_hidden(k1_funct_1(A_710,D_709),k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_8715,c_26])).

tff(c_8808,plain,(
    ! [D_94] :
      ( r2_hidden(D_94,k10_relat_1('#skF_13',k9_relat_1('#skF_13','#skF_11')))
      | ~ r2_hidden(D_94,k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_44,c_8771])).

tff(c_8823,plain,(
    ! [D_711] :
      ( r2_hidden(D_711,k10_relat_1('#skF_13',k9_relat_1('#skF_13','#skF_11')))
      | ~ r2_hidden(D_711,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_8808])).

tff(c_3552,plain,(
    ! [A_371,B_372] :
      ( k1_funct_1(A_371,'#skF_8'(A_371,B_372)) = '#skF_7'(A_371,B_372)
      | r2_hidden('#skF_9'(A_371,B_372),B_372)
      | k2_relat_1(A_371) = B_372
      | ~ v1_funct_1(A_371)
      | ~ v1_relat_1(A_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3564,plain,(
    ! [A_371,B_372,B_50] :
      ( r2_hidden('#skF_7'(A_371,B_372),B_50)
      | ~ r2_hidden('#skF_8'(A_371,B_372),k10_relat_1(A_371,B_50))
      | ~ v1_funct_1(A_371)
      | ~ v1_relat_1(A_371)
      | r2_hidden('#skF_9'(A_371,B_372),B_372)
      | k2_relat_1(A_371) = B_372
      | ~ v1_funct_1(A_371)
      | ~ v1_relat_1(A_371) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3552,c_28])).

tff(c_8829,plain,(
    ! [B_372] :
      ( r2_hidden('#skF_7'('#skF_13',B_372),k9_relat_1('#skF_13','#skF_11'))
      | r2_hidden('#skF_9'('#skF_13',B_372),B_372)
      | k2_relat_1('#skF_13') = B_372
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden('#skF_8'('#skF_13',B_372),'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_8823,c_3564])).

tff(c_9833,plain,(
    ! [B_735] :
      ( r2_hidden('#skF_7'('#skF_13',B_735),k9_relat_1('#skF_13','#skF_11'))
      | r2_hidden('#skF_9'('#skF_13',B_735),B_735)
      | k2_relat_1('#skF_13') = B_735
      | ~ r2_hidden('#skF_8'('#skF_13',B_735),'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_8829])).

tff(c_56,plain,(
    ! [A_55,B_77] :
      ( ~ r2_hidden('#skF_7'(A_55,B_77),B_77)
      | r2_hidden('#skF_9'(A_55,B_77),B_77)
      | k2_relat_1(A_55) = B_77
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9851,plain,
    ( ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13')
    | r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k9_relat_1('#skF_13','#skF_11'))
    | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13')
    | ~ r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11') ),
    inference(resolution,[status(thm)],[c_9833,c_56])).

tff(c_9924,plain,
    ( r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k9_relat_1('#skF_13','#skF_11'))
    | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13')
    | ~ r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_9851])).

tff(c_9925,plain,
    ( r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k9_relat_1('#skF_13','#skF_11'))
    | ~ r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_3549,c_9924])).

tff(c_9942,plain,(
    ~ r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_9925])).

tff(c_60,plain,(
    ! [A_55,B_77] :
      ( r2_hidden('#skF_8'(A_55,B_77),k1_relat_1(A_55))
      | r2_hidden('#skF_9'(A_55,B_77),B_77)
      | k2_relat_1(A_55) = B_77
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [A_1,E_42,B_24] :
      ( r2_hidden(k1_funct_1(A_1,E_42),k9_relat_1(A_1,B_24))
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_23032,plain,(
    ! [A_1238,B_1239,B_1240] :
      ( r2_hidden('#skF_7'(A_1238,B_1239),k9_relat_1(A_1238,B_1240))
      | ~ r2_hidden('#skF_8'(A_1238,B_1239),B_1240)
      | ~ r2_hidden('#skF_8'(A_1238,B_1239),k1_relat_1(A_1238))
      | ~ v1_funct_1(A_1238)
      | ~ v1_relat_1(A_1238)
      | r2_hidden('#skF_9'(A_1238,B_1239),B_1239)
      | k2_relat_1(A_1238) = B_1239
      | ~ v1_funct_1(A_1238)
      | ~ v1_relat_1(A_1238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3552,c_2])).

tff(c_23049,plain,(
    ! [A_55,B_77,B_1240] :
      ( r2_hidden('#skF_7'(A_55,B_77),k9_relat_1(A_55,B_1240))
      | ~ r2_hidden('#skF_8'(A_55,B_77),B_1240)
      | r2_hidden('#skF_9'(A_55,B_77),B_77)
      | k2_relat_1(A_55) = B_77
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(resolution,[status(thm)],[c_60,c_23032])).

tff(c_8,plain,(
    ! [A_1,B_24,D_39] :
      ( r2_hidden('#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39),k1_relat_1(A_1))
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_25235,plain,(
    ! [D_1315,A_1316,B_1317,B_1318] :
      ( r2_hidden(D_1315,k9_relat_1(A_1316,B_1317))
      | ~ r2_hidden('#skF_4'(A_1316,B_1318,k9_relat_1(A_1316,B_1318),D_1315),B_1317)
      | ~ r2_hidden('#skF_4'(A_1316,B_1318,k9_relat_1(A_1316,B_1318),D_1315),k1_relat_1(A_1316))
      | ~ v1_funct_1(A_1316)
      | ~ v1_relat_1(A_1316)
      | ~ r2_hidden(D_1315,k9_relat_1(A_1316,B_1318))
      | ~ v1_funct_1(A_1316)
      | ~ v1_relat_1(A_1316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_2])).

tff(c_25305,plain,(
    ! [D_1319,A_1320,B_1321] :
      ( r2_hidden(D_1319,k9_relat_1(A_1320,k1_relat_1(A_1320)))
      | ~ r2_hidden('#skF_4'(A_1320,B_1321,k9_relat_1(A_1320,B_1321),D_1319),k1_relat_1(A_1320))
      | ~ r2_hidden(D_1319,k9_relat_1(A_1320,B_1321))
      | ~ v1_funct_1(A_1320)
      | ~ v1_relat_1(A_1320) ) ),
    inference(resolution,[status(thm)],[c_8,c_25235])).

tff(c_25325,plain,(
    ! [D_1322,A_1323,B_1324] :
      ( r2_hidden(D_1322,k9_relat_1(A_1323,k1_relat_1(A_1323)))
      | ~ r2_hidden(D_1322,k9_relat_1(A_1323,B_1324))
      | ~ v1_funct_1(A_1323)
      | ~ v1_relat_1(A_1323) ) ),
    inference(resolution,[status(thm)],[c_8,c_25305])).

tff(c_28048,plain,(
    ! [A_1367,B_1368,B_1369] :
      ( r2_hidden('#skF_7'(A_1367,B_1368),k9_relat_1(A_1367,k1_relat_1(A_1367)))
      | ~ r2_hidden('#skF_8'(A_1367,B_1368),B_1369)
      | r2_hidden('#skF_9'(A_1367,B_1368),B_1368)
      | k2_relat_1(A_1367) = B_1368
      | ~ v1_funct_1(A_1367)
      | ~ v1_relat_1(A_1367) ) ),
    inference(resolution,[status(thm)],[c_23049,c_25325])).

tff(c_28127,plain,(
    ! [A_1370,B_1371] :
      ( r2_hidden('#skF_7'(A_1370,B_1371),k9_relat_1(A_1370,k1_relat_1(A_1370)))
      | r2_hidden('#skF_9'(A_1370,B_1371),B_1371)
      | k2_relat_1(A_1370) = B_1371
      | ~ v1_funct_1(A_1370)
      | ~ v1_relat_1(A_1370) ) ),
    inference(resolution,[status(thm)],[c_60,c_28048])).

tff(c_28420,plain,(
    ! [A_1374] :
      ( r2_hidden('#skF_9'(A_1374,k9_relat_1(A_1374,k1_relat_1(A_1374))),k9_relat_1(A_1374,k1_relat_1(A_1374)))
      | k9_relat_1(A_1374,k1_relat_1(A_1374)) = k2_relat_1(A_1374)
      | ~ v1_funct_1(A_1374)
      | ~ v1_relat_1(A_1374) ) ),
    inference(resolution,[status(thm)],[c_28127,c_56])).

tff(c_163,plain,(
    ! [D_129,A_130,B_131] :
      ( r2_hidden(D_129,k10_relat_1(A_130,B_131))
      | ~ r2_hidden(k1_funct_1(A_130,D_129),B_131)
      | ~ r2_hidden(D_129,k1_relat_1(A_130))
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_177,plain,(
    ! [D_94,A_55] :
      ( r2_hidden(D_94,k10_relat_1(A_55,k2_relat_1(A_55)))
      | ~ r2_hidden(D_94,k1_relat_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(resolution,[status(thm)],[c_44,c_163])).

tff(c_4596,plain,(
    ! [D_475,B_476,A_477,B_478] :
      ( r2_hidden(D_475,B_476)
      | ~ r2_hidden('#skF_4'(A_477,B_478,k9_relat_1(A_477,B_478),D_475),k10_relat_1(A_477,B_476))
      | ~ v1_funct_1(A_477)
      | ~ v1_relat_1(A_477)
      | ~ r2_hidden(D_475,k9_relat_1(A_477,B_478))
      | ~ v1_funct_1(A_477)
      | ~ v1_relat_1(A_477) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_28])).

tff(c_4848,plain,(
    ! [D_491,A_492,B_493] :
      ( r2_hidden(D_491,k2_relat_1(A_492))
      | ~ r2_hidden(D_491,k9_relat_1(A_492,B_493))
      | ~ r2_hidden('#skF_4'(A_492,B_493,k9_relat_1(A_492,B_493),D_491),k1_relat_1(A_492))
      | ~ v1_funct_1(A_492)
      | ~ v1_relat_1(A_492) ) ),
    inference(resolution,[status(thm)],[c_177,c_4596])).

tff(c_4859,plain,(
    ! [D_39,A_1,B_24] :
      ( r2_hidden(D_39,k2_relat_1(A_1))
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_8,c_4848])).

tff(c_28455,plain,(
    ! [A_1374] :
      ( r2_hidden('#skF_9'(A_1374,k9_relat_1(A_1374,k1_relat_1(A_1374))),k2_relat_1(A_1374))
      | k9_relat_1(A_1374,k1_relat_1(A_1374)) = k2_relat_1(A_1374)
      | ~ v1_funct_1(A_1374)
      | ~ v1_relat_1(A_1374) ) ),
    inference(resolution,[status(thm)],[c_28420,c_4859])).

tff(c_3917,plain,(
    ! [A_403,B_404,D_405] :
      ( r2_hidden('#skF_8'(A_403,B_404),k1_relat_1(A_403))
      | k1_funct_1(A_403,D_405) != '#skF_9'(A_403,B_404)
      | ~ r2_hidden(D_405,k1_relat_1(A_403))
      | k2_relat_1(A_403) = B_404
      | ~ v1_funct_1(A_403)
      | ~ v1_relat_1(A_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3923,plain,(
    ! [A_55,B_404,C_91] :
      ( r2_hidden('#skF_8'(A_55,B_404),k1_relat_1(A_55))
      | C_91 != '#skF_9'(A_55,B_404)
      | ~ r2_hidden('#skF_10'(A_55,k2_relat_1(A_55),C_91),k1_relat_1(A_55))
      | k2_relat_1(A_55) = B_404
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55)
      | ~ r2_hidden(C_91,k2_relat_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3917])).

tff(c_47248,plain,(
    ! [A_1869,B_1870] :
      ( r2_hidden('#skF_8'(A_1869,B_1870),k1_relat_1(A_1869))
      | ~ r2_hidden('#skF_10'(A_1869,k2_relat_1(A_1869),'#skF_9'(A_1869,B_1870)),k1_relat_1(A_1869))
      | k2_relat_1(A_1869) = B_1870
      | ~ v1_funct_1(A_1869)
      | ~ v1_relat_1(A_1869)
      | ~ r2_hidden('#skF_9'(A_1869,B_1870),k2_relat_1(A_1869))
      | ~ v1_funct_1(A_1869)
      | ~ v1_relat_1(A_1869) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3923])).

tff(c_47255,plain,(
    ! [B_1870] :
      ( r2_hidden('#skF_8'('#skF_13',B_1870),k1_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),'#skF_9'('#skF_13',B_1870)),'#skF_11')
      | k2_relat_1('#skF_13') = B_1870
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden('#skF_9'('#skF_13',B_1870),k2_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_47248])).

tff(c_47347,plain,(
    ! [B_1872] :
      ( r2_hidden('#skF_8'('#skF_13',B_1872),'#skF_11')
      | ~ r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),'#skF_9'('#skF_13',B_1872)),'#skF_11')
      | k2_relat_1('#skF_13') = B_1872
      | ~ r2_hidden('#skF_9'('#skF_13',B_1872),k2_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_78,c_76,c_74,c_47255])).

tff(c_47352,plain,(
    ! [B_1873] :
      ( r2_hidden('#skF_8'('#skF_13',B_1873),'#skF_11')
      | k2_relat_1('#skF_13') = B_1873
      | ~ r2_hidden('#skF_9'('#skF_13',B_1873),k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_136,c_47347])).

tff(c_47361,plain,
    ( r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13',k1_relat_1('#skF_13'))),'#skF_11')
    | k9_relat_1('#skF_13',k1_relat_1('#skF_13')) = k2_relat_1('#skF_13')
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_28455,c_47352])).

tff(c_47422,plain,
    ( r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11')
    | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_74,c_47361])).

tff(c_47424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3549,c_9942,c_47422])).

tff(c_47425,plain,(
    r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k9_relat_1('#skF_13','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_9925])).

tff(c_397,plain,(
    ! [A_157,B_158,D_159] :
      ( r2_hidden('#skF_4'(A_157,B_158,k9_relat_1(A_157,B_158),D_159),k1_relat_1(A_157))
      | ~ r2_hidden(D_159,k9_relat_1(A_157,B_158))
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_400,plain,(
    ! [B_158,D_159] :
      ( r2_hidden('#skF_4'('#skF_13',B_158,k9_relat_1('#skF_13',B_158),D_159),'#skF_11')
      | ~ r2_hidden(D_159,k9_relat_1('#skF_13',B_158))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_397])).

tff(c_402,plain,(
    ! [B_158,D_159] :
      ( r2_hidden('#skF_4'('#skF_13',B_158,k9_relat_1('#skF_13',B_158),D_159),'#skF_11')
      | ~ r2_hidden(D_159,k9_relat_1('#skF_13',B_158)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_400])).

tff(c_4858,plain,(
    ! [D_491,B_493] :
      ( r2_hidden(D_491,k2_relat_1('#skF_13'))
      | ~ r2_hidden(D_491,k9_relat_1('#skF_13',B_493))
      | ~ r2_hidden('#skF_4'('#skF_13',B_493,k9_relat_1('#skF_13',B_493),D_491),'#skF_11')
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_4848])).

tff(c_4968,plain,(
    ! [D_497,B_498] :
      ( r2_hidden(D_497,k2_relat_1('#skF_13'))
      | ~ r2_hidden(D_497,k9_relat_1('#skF_13',B_498))
      | ~ r2_hidden('#skF_4'('#skF_13',B_498,k9_relat_1('#skF_13',B_498),D_497),'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_4858])).

tff(c_4976,plain,(
    ! [D_159,B_158] :
      ( r2_hidden(D_159,k2_relat_1('#skF_13'))
      | ~ r2_hidden(D_159,k9_relat_1('#skF_13',B_158)) ) ),
    inference(resolution,[status(thm)],[c_402,c_4968])).

tff(c_47440,plain,(
    r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_47425,c_4976])).

tff(c_48,plain,(
    ! [A_55,C_91] :
      ( r2_hidden('#skF_10'(A_55,k2_relat_1(A_55),C_91),k1_relat_1(A_55))
      | ~ r2_hidden(C_91,k2_relat_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4156,plain,(
    ! [A_426,B_427,D_428] :
      ( k1_funct_1(A_426,'#skF_8'(A_426,B_427)) = '#skF_7'(A_426,B_427)
      | k1_funct_1(A_426,D_428) != '#skF_9'(A_426,B_427)
      | ~ r2_hidden(D_428,k1_relat_1(A_426))
      | k2_relat_1(A_426) = B_427
      | ~ v1_funct_1(A_426)
      | ~ v1_relat_1(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4164,plain,(
    ! [A_55,B_427,C_91] :
      ( k1_funct_1(A_55,'#skF_8'(A_55,B_427)) = '#skF_7'(A_55,B_427)
      | C_91 != '#skF_9'(A_55,B_427)
      | ~ r2_hidden('#skF_10'(A_55,k2_relat_1(A_55),C_91),k1_relat_1(A_55))
      | k2_relat_1(A_55) = B_427
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55)
      | ~ r2_hidden(C_91,k2_relat_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4156])).

tff(c_92863,plain,(
    ! [A_3250,B_3251] :
      ( k1_funct_1(A_3250,'#skF_8'(A_3250,B_3251)) = '#skF_7'(A_3250,B_3251)
      | ~ r2_hidden('#skF_10'(A_3250,k2_relat_1(A_3250),'#skF_9'(A_3250,B_3251)),k1_relat_1(A_3250))
      | k2_relat_1(A_3250) = B_3251
      | ~ v1_funct_1(A_3250)
      | ~ v1_relat_1(A_3250)
      | ~ r2_hidden('#skF_9'(A_3250,B_3251),k2_relat_1(A_3250))
      | ~ v1_funct_1(A_3250)
      | ~ v1_relat_1(A_3250) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4164])).

tff(c_92874,plain,(
    ! [A_3252,B_3253] :
      ( k1_funct_1(A_3252,'#skF_8'(A_3252,B_3253)) = '#skF_7'(A_3252,B_3253)
      | k2_relat_1(A_3252) = B_3253
      | ~ r2_hidden('#skF_9'(A_3252,B_3253),k2_relat_1(A_3252))
      | ~ v1_funct_1(A_3252)
      | ~ v1_relat_1(A_3252) ) ),
    inference(resolution,[status(thm)],[c_48,c_92863])).

tff(c_92904,plain,
    ( k1_funct_1('#skF_13','#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11'))) = '#skF_7'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
    | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13')
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_47440,c_92874])).

tff(c_92938,plain,
    ( k1_funct_1('#skF_13','#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11'))) = '#skF_7'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
    | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_92904])).

tff(c_92939,plain,(
    k1_funct_1('#skF_13','#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11'))) = '#skF_7'('#skF_13',k9_relat_1('#skF_13','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_3549,c_92938])).

tff(c_47426,plain,(
    r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_9925])).

tff(c_76577,plain,(
    ! [D_2894,A_2895,B_2896,B_2897] :
      ( r2_hidden(D_2894,k9_relat_1(A_2895,B_2896))
      | ~ r2_hidden('#skF_4'(A_2895,B_2897,k9_relat_1(A_2895,B_2897),D_2894),B_2896)
      | ~ r2_hidden('#skF_4'(A_2895,B_2897,k9_relat_1(A_2895,B_2897),D_2894),k1_relat_1(A_2895))
      | ~ v1_funct_1(A_2895)
      | ~ v1_relat_1(A_2895)
      | ~ r2_hidden(D_2894,k9_relat_1(A_2895,B_2897))
      | ~ v1_funct_1(A_2895)
      | ~ v1_relat_1(A_2895) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_2])).

tff(c_76666,plain,(
    ! [D_2899,A_2900,B_2901] :
      ( r2_hidden(D_2899,k9_relat_1(A_2900,k1_relat_1(A_2900)))
      | ~ r2_hidden('#skF_4'(A_2900,B_2901,k9_relat_1(A_2900,B_2901),D_2899),k1_relat_1(A_2900))
      | ~ r2_hidden(D_2899,k9_relat_1(A_2900,B_2901))
      | ~ v1_funct_1(A_2900)
      | ~ v1_relat_1(A_2900) ) ),
    inference(resolution,[status(thm)],[c_8,c_76577])).

tff(c_76686,plain,(
    ! [D_2902,A_2903,B_2904] :
      ( r2_hidden(D_2902,k9_relat_1(A_2903,k1_relat_1(A_2903)))
      | ~ r2_hidden(D_2902,k9_relat_1(A_2903,B_2904))
      | ~ v1_funct_1(A_2903)
      | ~ v1_relat_1(A_2903) ) ),
    inference(resolution,[status(thm)],[c_8,c_76666])).

tff(c_77092,plain,(
    ! [A_2907,E_2908,B_2909] :
      ( r2_hidden(k1_funct_1(A_2907,E_2908),k9_relat_1(A_2907,k1_relat_1(A_2907)))
      | ~ r2_hidden(E_2908,B_2909)
      | ~ r2_hidden(E_2908,k1_relat_1(A_2907))
      | ~ v1_funct_1(A_2907)
      | ~ v1_relat_1(A_2907) ) ),
    inference(resolution,[status(thm)],[c_2,c_76686])).

tff(c_79386,plain,(
    ! [A_2940] :
      ( r2_hidden(k1_funct_1(A_2940,'#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11'))),k9_relat_1(A_2940,k1_relat_1(A_2940)))
      | ~ r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k1_relat_1(A_2940))
      | ~ v1_funct_1(A_2940)
      | ~ v1_relat_1(A_2940) ) ),
    inference(resolution,[status(thm)],[c_47426,c_77092])).

tff(c_321,plain,(
    ! [D_151,B_50,A_149,B_150] :
      ( r2_hidden(D_151,B_50)
      | ~ r2_hidden('#skF_4'(A_149,B_150,k9_relat_1(A_149,B_150),D_151),k10_relat_1(A_149,B_50))
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149)
      | ~ r2_hidden(D_151,k9_relat_1(A_149,B_150))
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_28])).

tff(c_8848,plain,(
    ! [D_151,B_150] :
      ( r2_hidden(D_151,k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden(D_151,k9_relat_1('#skF_13',B_150))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden('#skF_4'('#skF_13',B_150,k9_relat_1('#skF_13',B_150),D_151),'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_8823,c_321])).

tff(c_8933,plain,(
    ! [D_716,B_717] :
      ( r2_hidden(D_716,k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden(D_716,k9_relat_1('#skF_13',B_717))
      | ~ r2_hidden('#skF_4'('#skF_13',B_717,k9_relat_1('#skF_13',B_717),D_716),'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_8848])).

tff(c_8941,plain,(
    ! [D_159,B_158] :
      ( r2_hidden(D_159,k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden(D_159,k9_relat_1('#skF_13',B_158)) ) ),
    inference(resolution,[status(thm)],[c_402,c_8933])).

tff(c_79393,plain,
    ( r2_hidden(k1_funct_1('#skF_13','#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11'))),k9_relat_1('#skF_13','#skF_11'))
    | ~ r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k1_relat_1('#skF_13'))
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_79386,c_8941])).

tff(c_79419,plain,(
    r2_hidden(k1_funct_1('#skF_13','#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11'))),k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_47426,c_74,c_79393])).

tff(c_92961,plain,(
    r2_hidden('#skF_7'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92939,c_79419])).

tff(c_50,plain,(
    ! [A_55,B_77,D_90] :
      ( ~ r2_hidden('#skF_7'(A_55,B_77),B_77)
      | k1_funct_1(A_55,D_90) != '#skF_9'(A_55,B_77)
      | ~ r2_hidden(D_90,k1_relat_1(A_55))
      | k2_relat_1(A_55) = B_77
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93184,plain,(
    ! [D_90] :
      ( k1_funct_1('#skF_13',D_90) != '#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden(D_90,k1_relat_1('#skF_13'))
      | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13')
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_92961,c_50])).

tff(c_93209,plain,(
    ! [D_90] :
      ( k1_funct_1('#skF_13',D_90) != '#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden(D_90,'#skF_11')
      | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_93184])).

tff(c_93445,plain,(
    ! [D_3259] :
      ( k1_funct_1('#skF_13',D_3259) != '#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden(D_3259,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3549,c_93209])).

tff(c_93466,plain,(
    ! [C_91] :
      ( C_91 != '#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),C_91),'#skF_11')
      | ~ r2_hidden(C_91,k2_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_93445])).

tff(c_93960,plain,(
    ! [C_3268] :
      ( C_3268 != '#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),C_3268),'#skF_11')
      | ~ r2_hidden(C_3268,k2_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_93466])).

tff(c_93965,plain,(
    ~ r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_136,c_93960])).

tff(c_93967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93965,c_47440])).

tff(c_93968,plain,(
    ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_93996,plain,(
    ~ r1_tarski(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_93992,c_93968])).

tff(c_94066,plain,(
    ! [A_3299,B_3300] :
      ( r2_hidden('#skF_8'(A_3299,B_3300),k1_relat_1(A_3299))
      | r2_hidden('#skF_9'(A_3299,B_3300),B_3300)
      | k2_relat_1(A_3299) = B_3300
      | ~ v1_funct_1(A_3299)
      | ~ v1_relat_1(A_3299) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_94079,plain,(
    ! [B_3300] :
      ( r2_hidden('#skF_8'('#skF_13',B_3300),'#skF_11')
      | r2_hidden('#skF_9'('#skF_13',B_3300),B_3300)
      | k2_relat_1('#skF_13') = B_3300
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_94066])).

tff(c_94083,plain,(
    ! [B_3300] :
      ( r2_hidden('#skF_8'('#skF_13',B_3300),'#skF_11')
      | r2_hidden('#skF_9'('#skF_13',B_3300),B_3300)
      | k2_relat_1('#skF_13') = B_3300 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_94079])).

tff(c_94196,plain,(
    ! [A_3316,B_3317,D_3318] :
      ( k1_funct_1(A_3316,'#skF_4'(A_3316,B_3317,k9_relat_1(A_3316,B_3317),D_3318)) = D_3318
      | ~ r2_hidden(D_3318,k9_relat_1(A_3316,B_3317))
      | ~ v1_funct_1(A_3316)
      | ~ v1_relat_1(A_3316) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_94215,plain,(
    ! [D_3318,B_3317] :
      ( r2_hidden(D_3318,'#skF_12')
      | ~ r2_hidden('#skF_4'('#skF_13',B_3317,k9_relat_1('#skF_13',B_3317),D_3318),'#skF_11')
      | ~ r2_hidden(D_3318,k9_relat_1('#skF_13',B_3317))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94196,c_72])).

tff(c_94223,plain,(
    ! [D_3319,B_3320] :
      ( r2_hidden(D_3319,'#skF_12')
      | ~ r2_hidden('#skF_4'('#skF_13',B_3320,k9_relat_1('#skF_13',B_3320),D_3319),'#skF_11')
      | ~ r2_hidden(D_3319,k9_relat_1('#skF_13',B_3320)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_94215])).

tff(c_94227,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,'#skF_12')
      | ~ r2_hidden(D_39,k9_relat_1('#skF_13','#skF_11'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_6,c_94223])).

tff(c_94231,plain,(
    ! [D_3321] :
      ( r2_hidden(D_3321,'#skF_12')
      | ~ r2_hidden(D_3321,k9_relat_1('#skF_13','#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_94227])).

tff(c_94253,plain,
    ( r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_12')
    | r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11')
    | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_94083,c_94231])).

tff(c_94351,plain,(
    k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13') ),
    inference(splitLeft,[status(thm)],[c_94253])).

tff(c_94849,plain,(
    ! [A_3366,B_3367,C_3368] :
      ( r2_hidden('#skF_5'(A_3366,B_3367,C_3368),k1_relat_1(A_3366))
      | r2_hidden('#skF_6'(A_3366,B_3367,C_3368),C_3368)
      | k10_relat_1(A_3366,B_3367) = C_3368
      | ~ v1_funct_1(A_3366)
      | ~ v1_relat_1(A_3366) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_94879,plain,(
    ! [B_3367,C_3368] :
      ( r2_hidden('#skF_5'('#skF_13',B_3367,C_3368),'#skF_11')
      | r2_hidden('#skF_6'('#skF_13',B_3367,C_3368),C_3368)
      | k10_relat_1('#skF_13',B_3367) = C_3368
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_94849])).

tff(c_94888,plain,(
    ! [B_3367,C_3368] :
      ( r2_hidden('#skF_5'('#skF_13',B_3367,C_3368),'#skF_11')
      | r2_hidden('#skF_6'('#skF_13',B_3367,C_3368),C_3368)
      | k10_relat_1('#skF_13',B_3367) = C_3368 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_94879])).

tff(c_97045,plain,(
    ! [A_3527,B_3528,C_3529] :
      ( r2_hidden('#skF_5'(A_3527,B_3528,C_3529),k1_relat_1(A_3527))
      | ~ r2_hidden(k1_funct_1(A_3527,'#skF_6'(A_3527,B_3528,C_3529)),B_3528)
      | ~ r2_hidden('#skF_6'(A_3527,B_3528,C_3529),k1_relat_1(A_3527))
      | k10_relat_1(A_3527,B_3528) = C_3529
      | ~ v1_funct_1(A_3527)
      | ~ v1_relat_1(A_3527) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97109,plain,(
    ! [C_3529] :
      ( r2_hidden('#skF_5'('#skF_13','#skF_12',C_3529),k1_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_6'('#skF_13','#skF_12',C_3529),k1_relat_1('#skF_13'))
      | k10_relat_1('#skF_13','#skF_12') = C_3529
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden('#skF_6'('#skF_13','#skF_12',C_3529),'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_72,c_97045])).

tff(c_97130,plain,(
    ! [C_3530] :
      ( r2_hidden('#skF_5'('#skF_13','#skF_12',C_3530),'#skF_11')
      | k10_relat_1('#skF_13','#skF_12') = C_3530
      | ~ r2_hidden('#skF_6'('#skF_13','#skF_12',C_3530),'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_74,c_97109])).

tff(c_97148,plain,
    ( r2_hidden('#skF_5'('#skF_13','#skF_12','#skF_11'),'#skF_11')
    | k10_relat_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_94888,c_97130])).

tff(c_97152,plain,(
    k10_relat_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_97148])).

tff(c_97213,plain,
    ( r1_tarski(k9_relat_1('#skF_13','#skF_11'),'#skF_12')
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_97152,c_62])).

tff(c_97239,plain,(
    r1_tarski(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_94351,c_97213])).

tff(c_97241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93996,c_97239])).

tff(c_97243,plain,(
    k10_relat_1('#skF_13','#skF_12') != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_97148])).

tff(c_97242,plain,(
    r2_hidden('#skF_5'('#skF_13','#skF_12','#skF_11'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_97148])).

tff(c_97246,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_13','#skF_6'('#skF_13','#skF_12','#skF_11')),'#skF_12')
    | ~ r2_hidden('#skF_6'('#skF_13','#skF_12','#skF_11'),k1_relat_1('#skF_13'))
    | k10_relat_1('#skF_13','#skF_12') = '#skF_11'
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_97242,c_32])).

tff(c_97249,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_13','#skF_6'('#skF_13','#skF_12','#skF_11')),'#skF_12')
    | ~ r2_hidden('#skF_6'('#skF_13','#skF_12','#skF_11'),'#skF_11')
    | k10_relat_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_97246])).

tff(c_97250,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_13','#skF_6'('#skF_13','#skF_12','#skF_11')),'#skF_12')
    | ~ r2_hidden('#skF_6'('#skF_13','#skF_12','#skF_11'),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_97243,c_97249])).

tff(c_97251,plain,(
    ~ r2_hidden('#skF_6'('#skF_13','#skF_12','#skF_11'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_97250])).

tff(c_97259,plain,
    ( ~ r2_hidden('#skF_5'('#skF_13','#skF_12','#skF_11'),'#skF_11')
    | k10_relat_1('#skF_13','#skF_12') = '#skF_11'
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_38,c_97251])).

tff(c_97265,plain,(
    k10_relat_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_97242,c_97259])).

tff(c_97267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97243,c_97265])).

tff(c_97269,plain,(
    r2_hidden('#skF_6'('#skF_13','#skF_12','#skF_11'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_97250])).

tff(c_97268,plain,(
    ~ r2_hidden(k1_funct_1('#skF_13','#skF_6'('#skF_13','#skF_12','#skF_11')),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_97250])).

tff(c_97366,plain,(
    ~ r2_hidden('#skF_6'('#skF_13','#skF_12','#skF_11'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_72,c_97268])).

tff(c_97373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97269,c_97366])).

tff(c_97375,plain,(
    k9_relat_1('#skF_13','#skF_11') != k2_relat_1('#skF_13') ),
    inference(splitRight,[status(thm)],[c_94253])).

tff(c_94158,plain,(
    ! [A_3308,E_3309,B_3310] :
      ( r2_hidden(k1_funct_1(A_3308,E_3309),k9_relat_1(A_3308,B_3310))
      | ~ r2_hidden(E_3309,B_3310)
      | ~ r2_hidden(E_3309,k1_relat_1(A_3308))
      | ~ v1_funct_1(A_3308)
      | ~ v1_relat_1(A_3308) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_94165,plain,(
    ! [E_3309,A_3308,B_3310] :
      ( r2_hidden(E_3309,k10_relat_1(A_3308,k9_relat_1(A_3308,B_3310)))
      | ~ r2_hidden(E_3309,B_3310)
      | ~ r2_hidden(E_3309,k1_relat_1(A_3308))
      | ~ v1_funct_1(A_3308)
      | ~ v1_relat_1(A_3308) ) ),
    inference(resolution,[status(thm)],[c_94158,c_26])).

tff(c_93997,plain,(
    ! [A_3285,C_3286] :
      ( k1_funct_1(A_3285,'#skF_10'(A_3285,k2_relat_1(A_3285),C_3286)) = C_3286
      | ~ r2_hidden(C_3286,k2_relat_1(A_3285))
      | ~ v1_funct_1(A_3285)
      | ~ v1_relat_1(A_3285) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97985,plain,(
    ! [C_3591,B_3592,A_3593] :
      ( r2_hidden(C_3591,B_3592)
      | ~ r2_hidden('#skF_10'(A_3593,k2_relat_1(A_3593),C_3591),k10_relat_1(A_3593,B_3592))
      | ~ v1_funct_1(A_3593)
      | ~ v1_relat_1(A_3593)
      | ~ r2_hidden(C_3591,k2_relat_1(A_3593))
      | ~ v1_funct_1(A_3593)
      | ~ v1_relat_1(A_3593) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93997,c_28])).

tff(c_102505,plain,(
    ! [C_3878,A_3879,B_3880] :
      ( r2_hidden(C_3878,k9_relat_1(A_3879,B_3880))
      | ~ r2_hidden(C_3878,k2_relat_1(A_3879))
      | ~ r2_hidden('#skF_10'(A_3879,k2_relat_1(A_3879),C_3878),B_3880)
      | ~ r2_hidden('#skF_10'(A_3879,k2_relat_1(A_3879),C_3878),k1_relat_1(A_3879))
      | ~ v1_funct_1(A_3879)
      | ~ v1_relat_1(A_3879) ) ),
    inference(resolution,[status(thm)],[c_94165,c_97985])).

tff(c_102518,plain,(
    ! [C_3289] :
      ( r2_hidden(C_3289,k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),C_3289),k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden(C_3289,k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_94024,c_102505])).

tff(c_110194,plain,(
    ! [C_4193] :
      ( r2_hidden(C_4193,k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),C_4193),'#skF_11')
      | ~ r2_hidden(C_4193,k2_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_102518])).

tff(c_110199,plain,(
    ! [C_4194] :
      ( r2_hidden(C_4194,k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden(C_4194,k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_94024,c_110194])).

tff(c_110255,plain,(
    ! [D_4195,A_4196] :
      ( r2_hidden(D_4195,k10_relat_1(A_4196,k9_relat_1('#skF_13','#skF_11')))
      | ~ r2_hidden(D_4195,k1_relat_1(A_4196))
      | ~ v1_funct_1(A_4196)
      | ~ v1_relat_1(A_4196)
      | ~ r2_hidden(k1_funct_1(A_4196,D_4195),k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_110199,c_26])).

tff(c_110292,plain,(
    ! [D_94] :
      ( r2_hidden(D_94,k10_relat_1('#skF_13',k9_relat_1('#skF_13','#skF_11')))
      | ~ r2_hidden(D_94,k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_44,c_110255])).

tff(c_110307,plain,(
    ! [D_4197] :
      ( r2_hidden(D_4197,k10_relat_1('#skF_13',k9_relat_1('#skF_13','#skF_11')))
      | ~ r2_hidden(D_4197,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_110292])).

tff(c_97476,plain,(
    ! [A_3545,B_3546] :
      ( k1_funct_1(A_3545,'#skF_8'(A_3545,B_3546)) = '#skF_7'(A_3545,B_3546)
      | r2_hidden('#skF_9'(A_3545,B_3546),B_3546)
      | k2_relat_1(A_3545) = B_3546
      | ~ v1_funct_1(A_3545)
      | ~ v1_relat_1(A_3545) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97488,plain,(
    ! [A_3545,B_3546,B_50] :
      ( r2_hidden('#skF_7'(A_3545,B_3546),B_50)
      | ~ r2_hidden('#skF_8'(A_3545,B_3546),k10_relat_1(A_3545,B_50))
      | ~ v1_funct_1(A_3545)
      | ~ v1_relat_1(A_3545)
      | r2_hidden('#skF_9'(A_3545,B_3546),B_3546)
      | k2_relat_1(A_3545) = B_3546
      | ~ v1_funct_1(A_3545)
      | ~ v1_relat_1(A_3545) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97476,c_28])).

tff(c_110313,plain,(
    ! [B_3546] :
      ( r2_hidden('#skF_7'('#skF_13',B_3546),k9_relat_1('#skF_13','#skF_11'))
      | r2_hidden('#skF_9'('#skF_13',B_3546),B_3546)
      | k2_relat_1('#skF_13') = B_3546
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden('#skF_8'('#skF_13',B_3546),'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_110307,c_97488])).

tff(c_111402,plain,(
    ! [B_4220] :
      ( r2_hidden('#skF_7'('#skF_13',B_4220),k9_relat_1('#skF_13','#skF_11'))
      | r2_hidden('#skF_9'('#skF_13',B_4220),B_4220)
      | k2_relat_1('#skF_13') = B_4220
      | ~ r2_hidden('#skF_8'('#skF_13',B_4220),'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_110313])).

tff(c_111420,plain,
    ( ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13')
    | r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k9_relat_1('#skF_13','#skF_11'))
    | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13')
    | ~ r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11') ),
    inference(resolution,[status(thm)],[c_111402,c_56])).

tff(c_111493,plain,
    ( r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k9_relat_1('#skF_13','#skF_11'))
    | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13')
    | ~ r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_111420])).

tff(c_111494,plain,
    ( r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k9_relat_1('#skF_13','#skF_11'))
    | ~ r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_97375,c_111493])).

tff(c_111511,plain,(
    ~ r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_111494])).

tff(c_115188,plain,(
    ! [A_4372,B_4373,B_4374] :
      ( r2_hidden('#skF_7'(A_4372,B_4373),k9_relat_1(A_4372,B_4374))
      | ~ r2_hidden('#skF_8'(A_4372,B_4373),B_4374)
      | ~ r2_hidden('#skF_8'(A_4372,B_4373),k1_relat_1(A_4372))
      | ~ v1_funct_1(A_4372)
      | ~ v1_relat_1(A_4372)
      | r2_hidden('#skF_9'(A_4372,B_4373),B_4373)
      | k2_relat_1(A_4372) = B_4373
      | ~ v1_funct_1(A_4372)
      | ~ v1_relat_1(A_4372) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97476,c_2])).

tff(c_115205,plain,(
    ! [A_55,B_77,B_4374] :
      ( r2_hidden('#skF_7'(A_55,B_77),k9_relat_1(A_55,B_4374))
      | ~ r2_hidden('#skF_8'(A_55,B_77),B_4374)
      | r2_hidden('#skF_9'(A_55,B_77),B_77)
      | k2_relat_1(A_55) = B_77
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(resolution,[status(thm)],[c_60,c_115188])).

tff(c_117795,plain,(
    ! [D_4465,A_4466,B_4467,B_4468] :
      ( r2_hidden(D_4465,k9_relat_1(A_4466,B_4467))
      | ~ r2_hidden('#skF_4'(A_4466,B_4468,k9_relat_1(A_4466,B_4468),D_4465),B_4467)
      | ~ r2_hidden('#skF_4'(A_4466,B_4468,k9_relat_1(A_4466,B_4468),D_4465),k1_relat_1(A_4466))
      | ~ v1_funct_1(A_4466)
      | ~ v1_relat_1(A_4466)
      | ~ r2_hidden(D_4465,k9_relat_1(A_4466,B_4468))
      | ~ v1_funct_1(A_4466)
      | ~ v1_relat_1(A_4466) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94196,c_2])).

tff(c_117861,plain,(
    ! [D_4469,A_4470,B_4471] :
      ( r2_hidden(D_4469,k9_relat_1(A_4470,k1_relat_1(A_4470)))
      | ~ r2_hidden('#skF_4'(A_4470,B_4471,k9_relat_1(A_4470,B_4471),D_4469),k1_relat_1(A_4470))
      | ~ r2_hidden(D_4469,k9_relat_1(A_4470,B_4471))
      | ~ v1_funct_1(A_4470)
      | ~ v1_relat_1(A_4470) ) ),
    inference(resolution,[status(thm)],[c_8,c_117795])).

tff(c_117881,plain,(
    ! [D_4472,A_4473,B_4474] :
      ( r2_hidden(D_4472,k9_relat_1(A_4473,k1_relat_1(A_4473)))
      | ~ r2_hidden(D_4472,k9_relat_1(A_4473,B_4474))
      | ~ v1_funct_1(A_4473)
      | ~ v1_relat_1(A_4473) ) ),
    inference(resolution,[status(thm)],[c_8,c_117861])).

tff(c_120956,plain,(
    ! [A_4523,B_4524,B_4525] :
      ( r2_hidden('#skF_7'(A_4523,B_4524),k9_relat_1(A_4523,k1_relat_1(A_4523)))
      | ~ r2_hidden('#skF_8'(A_4523,B_4524),B_4525)
      | r2_hidden('#skF_9'(A_4523,B_4524),B_4524)
      | k2_relat_1(A_4523) = B_4524
      | ~ v1_funct_1(A_4523)
      | ~ v1_relat_1(A_4523) ) ),
    inference(resolution,[status(thm)],[c_115205,c_117881])).

tff(c_121037,plain,(
    ! [A_4526,B_4527] :
      ( r2_hidden('#skF_7'(A_4526,B_4527),k9_relat_1(A_4526,k1_relat_1(A_4526)))
      | r2_hidden('#skF_9'(A_4526,B_4527),B_4527)
      | k2_relat_1(A_4526) = B_4527
      | ~ v1_funct_1(A_4526)
      | ~ v1_relat_1(A_4526) ) ),
    inference(resolution,[status(thm)],[c_60,c_120956])).

tff(c_121181,plain,(
    ! [A_4528] :
      ( r2_hidden('#skF_9'(A_4528,k9_relat_1(A_4528,k1_relat_1(A_4528))),k9_relat_1(A_4528,k1_relat_1(A_4528)))
      | k9_relat_1(A_4528,k1_relat_1(A_4528)) = k2_relat_1(A_4528)
      | ~ v1_funct_1(A_4528)
      | ~ v1_relat_1(A_4528) ) ),
    inference(resolution,[status(thm)],[c_121037,c_56])).

tff(c_98361,plain,(
    ! [D_3638,A_3639,B_3640] :
      ( r2_hidden(D_3638,k2_relat_1(A_3639))
      | ~ r2_hidden('#skF_4'(A_3639,B_3640,k9_relat_1(A_3639,B_3640),D_3638),k1_relat_1(A_3639))
      | ~ v1_funct_1(A_3639)
      | ~ v1_relat_1(A_3639)
      | ~ r2_hidden(D_3638,k9_relat_1(A_3639,B_3640))
      | ~ v1_funct_1(A_3639)
      | ~ v1_relat_1(A_3639) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94196,c_44])).

tff(c_98372,plain,(
    ! [D_39,A_1,B_24] :
      ( r2_hidden(D_39,k2_relat_1(A_1))
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_8,c_98361])).

tff(c_121216,plain,(
    ! [A_4528] :
      ( r2_hidden('#skF_9'(A_4528,k9_relat_1(A_4528,k1_relat_1(A_4528))),k2_relat_1(A_4528))
      | k9_relat_1(A_4528,k1_relat_1(A_4528)) = k2_relat_1(A_4528)
      | ~ v1_funct_1(A_4528)
      | ~ v1_relat_1(A_4528) ) ),
    inference(resolution,[status(thm)],[c_121181,c_98372])).

tff(c_97769,plain,(
    ! [A_3571,B_3572,D_3573] :
      ( r2_hidden('#skF_8'(A_3571,B_3572),k1_relat_1(A_3571))
      | k1_funct_1(A_3571,D_3573) != '#skF_9'(A_3571,B_3572)
      | ~ r2_hidden(D_3573,k1_relat_1(A_3571))
      | k2_relat_1(A_3571) = B_3572
      | ~ v1_funct_1(A_3571)
      | ~ v1_relat_1(A_3571) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97775,plain,(
    ! [A_55,B_3572,C_91] :
      ( r2_hidden('#skF_8'(A_55,B_3572),k1_relat_1(A_55))
      | C_91 != '#skF_9'(A_55,B_3572)
      | ~ r2_hidden('#skF_10'(A_55,k2_relat_1(A_55),C_91),k1_relat_1(A_55))
      | k2_relat_1(A_55) = B_3572
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55)
      | ~ r2_hidden(C_91,k2_relat_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_97769])).

tff(c_129877,plain,(
    ! [A_4753,B_4754] :
      ( r2_hidden('#skF_8'(A_4753,B_4754),k1_relat_1(A_4753))
      | ~ r2_hidden('#skF_10'(A_4753,k2_relat_1(A_4753),'#skF_9'(A_4753,B_4754)),k1_relat_1(A_4753))
      | k2_relat_1(A_4753) = B_4754
      | ~ v1_funct_1(A_4753)
      | ~ v1_relat_1(A_4753)
      | ~ r2_hidden('#skF_9'(A_4753,B_4754),k2_relat_1(A_4753))
      | ~ v1_funct_1(A_4753)
      | ~ v1_relat_1(A_4753) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_97775])).

tff(c_129888,plain,(
    ! [A_4755,B_4756] :
      ( r2_hidden('#skF_8'(A_4755,B_4756),k1_relat_1(A_4755))
      | k2_relat_1(A_4755) = B_4756
      | ~ r2_hidden('#skF_9'(A_4755,B_4756),k2_relat_1(A_4755))
      | ~ v1_funct_1(A_4755)
      | ~ v1_relat_1(A_4755) ) ),
    inference(resolution,[status(thm)],[c_48,c_129877])).

tff(c_129911,plain,(
    ! [B_4756] :
      ( r2_hidden('#skF_8'('#skF_13',B_4756),'#skF_11')
      | k2_relat_1('#skF_13') = B_4756
      | ~ r2_hidden('#skF_9'('#skF_13',B_4756),k2_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_129888])).

tff(c_129930,plain,(
    ! [B_4757] :
      ( r2_hidden('#skF_8'('#skF_13',B_4757),'#skF_11')
      | k2_relat_1('#skF_13') = B_4757
      | ~ r2_hidden('#skF_9'('#skF_13',B_4757),k2_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_129911])).

tff(c_129936,plain,
    ( r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13',k1_relat_1('#skF_13'))),'#skF_11')
    | k9_relat_1('#skF_13',k1_relat_1('#skF_13')) = k2_relat_1('#skF_13')
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_121216,c_129930])).

tff(c_129994,plain,
    ( r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11')
    | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_74,c_129936])).

tff(c_129996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97375,c_111511,c_129994])).

tff(c_129997,plain,(
    r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k9_relat_1('#skF_13','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_111494])).

tff(c_94284,plain,(
    ! [A_3324,B_3325,D_3326] :
      ( r2_hidden('#skF_4'(A_3324,B_3325,k9_relat_1(A_3324,B_3325),D_3326),k1_relat_1(A_3324))
      | ~ r2_hidden(D_3326,k9_relat_1(A_3324,B_3325))
      | ~ v1_funct_1(A_3324)
      | ~ v1_relat_1(A_3324) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_94287,plain,(
    ! [B_3325,D_3326] :
      ( r2_hidden('#skF_4'('#skF_13',B_3325,k9_relat_1('#skF_13',B_3325),D_3326),'#skF_11')
      | ~ r2_hidden(D_3326,k9_relat_1('#skF_13',B_3325))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_94284])).

tff(c_94289,plain,(
    ! [B_3325,D_3326] :
      ( r2_hidden('#skF_4'('#skF_13',B_3325,k9_relat_1('#skF_13',B_3325),D_3326),'#skF_11')
      | ~ r2_hidden(D_3326,k9_relat_1('#skF_13',B_3325)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_94287])).

tff(c_98371,plain,(
    ! [D_3638,B_3640] :
      ( r2_hidden(D_3638,k2_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_4'('#skF_13',B_3640,k9_relat_1('#skF_13',B_3640),D_3638),'#skF_11')
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden(D_3638,k9_relat_1('#skF_13',B_3640))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_98361])).

tff(c_98481,plain,(
    ! [D_3644,B_3645] :
      ( r2_hidden(D_3644,k2_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_4'('#skF_13',B_3645,k9_relat_1('#skF_13',B_3645),D_3644),'#skF_11')
      | ~ r2_hidden(D_3644,k9_relat_1('#skF_13',B_3645)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_78,c_76,c_98371])).

tff(c_98489,plain,(
    ! [D_3326,B_3325] :
      ( r2_hidden(D_3326,k2_relat_1('#skF_13'))
      | ~ r2_hidden(D_3326,k9_relat_1('#skF_13',B_3325)) ) ),
    inference(resolution,[status(thm)],[c_94289,c_98481])).

tff(c_130030,plain,(
    r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_129997,c_98489])).

tff(c_98008,plain,(
    ! [A_3594,B_3595,D_3596] :
      ( k1_funct_1(A_3594,'#skF_8'(A_3594,B_3595)) = '#skF_7'(A_3594,B_3595)
      | k1_funct_1(A_3594,D_3596) != '#skF_9'(A_3594,B_3595)
      | ~ r2_hidden(D_3596,k1_relat_1(A_3594))
      | k2_relat_1(A_3594) = B_3595
      | ~ v1_funct_1(A_3594)
      | ~ v1_relat_1(A_3594) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_98016,plain,(
    ! [A_55,B_3595,C_91] :
      ( k1_funct_1(A_55,'#skF_8'(A_55,B_3595)) = '#skF_7'(A_55,B_3595)
      | C_91 != '#skF_9'(A_55,B_3595)
      | ~ r2_hidden('#skF_10'(A_55,k2_relat_1(A_55),C_91),k1_relat_1(A_55))
      | k2_relat_1(A_55) = B_3595
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55)
      | ~ r2_hidden(C_91,k2_relat_1(A_55))
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_98008])).

tff(c_153756,plain,(
    ! [A_5369,B_5370] :
      ( k1_funct_1(A_5369,'#skF_8'(A_5369,B_5370)) = '#skF_7'(A_5369,B_5370)
      | ~ r2_hidden('#skF_10'(A_5369,k2_relat_1(A_5369),'#skF_9'(A_5369,B_5370)),k1_relat_1(A_5369))
      | k2_relat_1(A_5369) = B_5370
      | ~ v1_funct_1(A_5369)
      | ~ v1_relat_1(A_5369)
      | ~ r2_hidden('#skF_9'(A_5369,B_5370),k2_relat_1(A_5369))
      | ~ v1_funct_1(A_5369)
      | ~ v1_relat_1(A_5369) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_98016])).

tff(c_153767,plain,(
    ! [A_5371,B_5372] :
      ( k1_funct_1(A_5371,'#skF_8'(A_5371,B_5372)) = '#skF_7'(A_5371,B_5372)
      | k2_relat_1(A_5371) = B_5372
      | ~ r2_hidden('#skF_9'(A_5371,B_5372),k2_relat_1(A_5371))
      | ~ v1_funct_1(A_5371)
      | ~ v1_relat_1(A_5371) ) ),
    inference(resolution,[status(thm)],[c_48,c_153756])).

tff(c_153797,plain,
    ( k1_funct_1('#skF_13','#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11'))) = '#skF_7'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
    | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13')
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_130030,c_153767])).

tff(c_153831,plain,
    ( k1_funct_1('#skF_13','#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11'))) = '#skF_7'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
    | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_153797])).

tff(c_153832,plain,(
    k1_funct_1('#skF_13','#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11'))) = '#skF_7'('#skF_13',k9_relat_1('#skF_13','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_97375,c_153831])).

tff(c_129998,plain,(
    r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_111494])).

tff(c_136491,plain,(
    ! [D_5019,A_5020,B_5021,B_5022] :
      ( r2_hidden(D_5019,k9_relat_1(A_5020,B_5021))
      | ~ r2_hidden('#skF_4'(A_5020,B_5022,k9_relat_1(A_5020,B_5022),D_5019),B_5021)
      | ~ r2_hidden('#skF_4'(A_5020,B_5022,k9_relat_1(A_5020,B_5022),D_5019),k1_relat_1(A_5020))
      | ~ v1_funct_1(A_5020)
      | ~ v1_relat_1(A_5020)
      | ~ r2_hidden(D_5019,k9_relat_1(A_5020,B_5022))
      | ~ v1_funct_1(A_5020)
      | ~ v1_relat_1(A_5020) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94196,c_2])).

tff(c_136561,plain,(
    ! [D_5023,A_5024,B_5025] :
      ( r2_hidden(D_5023,k9_relat_1(A_5024,k1_relat_1(A_5024)))
      | ~ r2_hidden('#skF_4'(A_5024,B_5025,k9_relat_1(A_5024,B_5025),D_5023),k1_relat_1(A_5024))
      | ~ r2_hidden(D_5023,k9_relat_1(A_5024,B_5025))
      | ~ v1_funct_1(A_5024)
      | ~ v1_relat_1(A_5024) ) ),
    inference(resolution,[status(thm)],[c_8,c_136491])).

tff(c_136581,plain,(
    ! [D_5026,A_5027,B_5028] :
      ( r2_hidden(D_5026,k9_relat_1(A_5027,k1_relat_1(A_5027)))
      | ~ r2_hidden(D_5026,k9_relat_1(A_5027,B_5028))
      | ~ v1_funct_1(A_5027)
      | ~ v1_relat_1(A_5027) ) ),
    inference(resolution,[status(thm)],[c_8,c_136561])).

tff(c_136987,plain,(
    ! [A_5031,E_5032,B_5033] :
      ( r2_hidden(k1_funct_1(A_5031,E_5032),k9_relat_1(A_5031,k1_relat_1(A_5031)))
      | ~ r2_hidden(E_5032,B_5033)
      | ~ r2_hidden(E_5032,k1_relat_1(A_5031))
      | ~ v1_funct_1(A_5031)
      | ~ v1_relat_1(A_5031) ) ),
    inference(resolution,[status(thm)],[c_2,c_136581])).

tff(c_139497,plain,(
    ! [A_5070] :
      ( r2_hidden(k1_funct_1(A_5070,'#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11'))),k9_relat_1(A_5070,k1_relat_1(A_5070)))
      | ~ r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k1_relat_1(A_5070))
      | ~ v1_funct_1(A_5070)
      | ~ v1_relat_1(A_5070) ) ),
    inference(resolution,[status(thm)],[c_129998,c_136987])).

tff(c_139525,plain,
    ( r2_hidden(k1_funct_1('#skF_13','#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11'))),k9_relat_1('#skF_13','#skF_11'))
    | ~ r2_hidden('#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k1_relat_1('#skF_13'))
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_139497])).

tff(c_139540,plain,(
    r2_hidden(k1_funct_1('#skF_13','#skF_8'('#skF_13',k9_relat_1('#skF_13','#skF_11'))),k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_129998,c_74,c_139525])).

tff(c_153857,plain,(
    r2_hidden('#skF_7'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k9_relat_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153832,c_139540])).

tff(c_154078,plain,(
    ! [D_90] :
      ( k1_funct_1('#skF_13',D_90) != '#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden(D_90,k1_relat_1('#skF_13'))
      | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13')
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_153857,c_50])).

tff(c_154103,plain,(
    ! [D_90] :
      ( k1_funct_1('#skF_13',D_90) != '#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden(D_90,'#skF_11')
      | k9_relat_1('#skF_13','#skF_11') = k2_relat_1('#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_154078])).

tff(c_154358,plain,(
    ! [D_5378] :
      ( k1_funct_1('#skF_13',D_5378) != '#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden(D_5378,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_97375,c_154103])).

tff(c_154379,plain,(
    ! [C_91] :
      ( C_91 != '#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),C_91),'#skF_11')
      | ~ r2_hidden(C_91,k2_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_154358])).

tff(c_154862,plain,(
    ! [C_5384] :
      ( C_5384 != '#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11'))
      | ~ r2_hidden('#skF_10'('#skF_13',k2_relat_1('#skF_13'),C_5384),'#skF_11')
      | ~ r2_hidden(C_5384,k2_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_154379])).

tff(c_154867,plain,(
    ~ r2_hidden('#skF_9'('#skF_13',k9_relat_1('#skF_13','#skF_11')),k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_94024,c_154862])).

tff(c_154869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154867,c_130030])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:21:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 42.19/30.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.19/30.52  
% 42.19/30.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.41/30.52  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_13 > #skF_5 > #skF_2 > #skF_8 > #skF_4 > #skF_3 > #skF_7 > #skF_9 > #skF_12 > #skF_10
% 42.41/30.52  
% 42.41/30.52  %Foreground sorts:
% 42.41/30.52  
% 42.41/30.52  
% 42.41/30.52  %Background operators:
% 42.41/30.52  
% 42.41/30.52  
% 42.41/30.52  %Foreground operators:
% 42.41/30.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 42.41/30.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 42.41/30.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 42.41/30.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 42.41/30.52  tff('#skF_11', type, '#skF_11': $i).
% 42.41/30.52  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 42.41/30.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 42.41/30.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 42.41/30.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 42.41/30.52  tff('#skF_13', type, '#skF_13': $i).
% 42.41/30.52  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 42.41/30.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 42.41/30.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 42.41/30.52  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 42.41/30.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 42.41/30.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 42.41/30.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 42.41/30.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 42.41/30.52  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 42.41/30.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 42.41/30.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 42.41/30.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 42.41/30.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 42.41/30.52  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 42.41/30.52  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 42.41/30.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 42.41/30.52  tff('#skF_12', type, '#skF_12': $i).
% 42.41/30.52  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 42.41/30.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 42.41/30.52  
% 42.41/30.56  tff(f_107, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 42.41/30.56  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 42.41/30.56  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 42.41/30.56  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 42.41/30.56  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 42.41/30.56  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 42.41/30.56  tff(c_78, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_107])).
% 42.41/30.56  tff(c_76, plain, (v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_107])).
% 42.41/30.56  tff(c_74, plain, (k1_relat_1('#skF_13')='#skF_11'), inference(cnfTransformation, [status(thm)], [f_107])).
% 42.41/30.56  tff(c_94019, plain, (![A_3288, C_3289]: (r2_hidden('#skF_10'(A_3288, k2_relat_1(A_3288), C_3289), k1_relat_1(A_3288)) | ~r2_hidden(C_3289, k2_relat_1(A_3288)) | ~v1_funct_1(A_3288) | ~v1_relat_1(A_3288))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_94022, plain, (![C_3289]: (r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), C_3289), '#skF_11') | ~r2_hidden(C_3289, k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_94019])).
% 42.41/30.56  tff(c_94024, plain, (![C_3289]: (r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), C_3289), '#skF_11') | ~r2_hidden(C_3289, k2_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_94022])).
% 42.41/30.56  tff(c_46, plain, (![A_55, C_91]: (k1_funct_1(A_55, '#skF_10'(A_55, k2_relat_1(A_55), C_91))=C_91 | ~r2_hidden(C_91, k2_relat_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_93986, plain, (![B_3282, A_3283]: (m1_subset_1(B_3282, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_3282), A_3283))) | ~r1_tarski(k2_relat_1(B_3282), A_3283) | ~v1_funct_1(B_3282) | ~v1_relat_1(B_3282))), inference(cnfTransformation, [status(thm)], [f_89])).
% 42.41/30.56  tff(c_93989, plain, (![A_3283]: (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', A_3283))) | ~r1_tarski(k2_relat_1('#skF_13'), A_3283) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_93986])).
% 42.41/30.56  tff(c_93992, plain, (![A_3284]: (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', A_3284))) | ~r1_tarski(k2_relat_1('#skF_13'), A_3284))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_93989])).
% 42.41/30.56  tff(c_131, plain, (![A_120, C_121]: (r2_hidden('#skF_10'(A_120, k2_relat_1(A_120), C_121), k1_relat_1(A_120)) | ~r2_hidden(C_121, k2_relat_1(A_120)) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_134, plain, (![C_121]: (r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), C_121), '#skF_11') | ~r2_hidden(C_121, k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_131])).
% 42.41/30.56  tff(c_136, plain, (![C_121]: (r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), C_121), '#skF_11') | ~r2_hidden(C_121, k2_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_134])).
% 42.41/30.56  tff(c_70, plain, (~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12'))) | ~v1_funct_2('#skF_13', '#skF_11', '#skF_12') | ~v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_107])).
% 42.41/30.56  tff(c_80, plain, (~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12'))) | ~v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70])).
% 42.41/30.56  tff(c_86, plain, (~v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(splitLeft, [status(thm)], [c_80])).
% 42.41/30.56  tff(c_244, plain, (![A_141, B_142]: (r2_hidden('#skF_8'(A_141, B_142), k1_relat_1(A_141)) | r2_hidden('#skF_9'(A_141, B_142), B_142) | k2_relat_1(A_141)=B_142 | ~v1_funct_1(A_141) | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_257, plain, (![B_142]: (r2_hidden('#skF_8'('#skF_13', B_142), '#skF_11') | r2_hidden('#skF_9'('#skF_13', B_142), B_142) | k2_relat_1('#skF_13')=B_142 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_244])).
% 42.41/30.56  tff(c_261, plain, (![B_142]: (r2_hidden('#skF_8'('#skF_13', B_142), '#skF_11') | r2_hidden('#skF_9'('#skF_13', B_142), B_142) | k2_relat_1('#skF_13')=B_142)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_257])).
% 42.41/30.56  tff(c_6, plain, (![A_1, B_24, D_39]: (r2_hidden('#skF_4'(A_1, B_24, k9_relat_1(A_1, B_24), D_39), B_24) | ~r2_hidden(D_39, k9_relat_1(A_1, B_24)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 42.41/30.56  tff(c_309, plain, (![A_149, B_150, D_151]: (k1_funct_1(A_149, '#skF_4'(A_149, B_150, k9_relat_1(A_149, B_150), D_151))=D_151 | ~r2_hidden(D_151, k9_relat_1(A_149, B_150)) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_42])).
% 42.41/30.56  tff(c_72, plain, (![D_100]: (r2_hidden(k1_funct_1('#skF_13', D_100), '#skF_12') | ~r2_hidden(D_100, '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 42.41/30.56  tff(c_328, plain, (![D_151, B_150]: (r2_hidden(D_151, '#skF_12') | ~r2_hidden('#skF_4'('#skF_13', B_150, k9_relat_1('#skF_13', B_150), D_151), '#skF_11') | ~r2_hidden(D_151, k9_relat_1('#skF_13', B_150)) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_309, c_72])).
% 42.41/30.56  tff(c_336, plain, (![D_152, B_153]: (r2_hidden(D_152, '#skF_12') | ~r2_hidden('#skF_4'('#skF_13', B_153, k9_relat_1('#skF_13', B_153), D_152), '#skF_11') | ~r2_hidden(D_152, k9_relat_1('#skF_13', B_153)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_328])).
% 42.41/30.56  tff(c_340, plain, (![D_39]: (r2_hidden(D_39, '#skF_12') | ~r2_hidden(D_39, k9_relat_1('#skF_13', '#skF_11')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_6, c_336])).
% 42.41/30.56  tff(c_344, plain, (![D_154]: (r2_hidden(D_154, '#skF_12') | ~r2_hidden(D_154, k9_relat_1('#skF_13', '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_340])).
% 42.41/30.56  tff(c_363, plain, (r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_12') | r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11') | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_261, c_344])).
% 42.41/30.56  tff(c_500, plain, (k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13')), inference(splitLeft, [status(thm)], [c_363])).
% 42.41/30.56  tff(c_890, plain, (![A_192, B_193, C_194]: (r2_hidden('#skF_5'(A_192, B_193, C_194), k1_relat_1(A_192)) | r2_hidden('#skF_6'(A_192, B_193, C_194), C_194) | k10_relat_1(A_192, B_193)=C_194 | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(cnfTransformation, [status(thm)], [f_56])).
% 42.41/30.56  tff(c_920, plain, (![B_193, C_194]: (r2_hidden('#skF_5'('#skF_13', B_193, C_194), '#skF_11') | r2_hidden('#skF_6'('#skF_13', B_193, C_194), C_194) | k10_relat_1('#skF_13', B_193)=C_194 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_890])).
% 42.41/30.56  tff(c_929, plain, (![B_193, C_194]: (r2_hidden('#skF_5'('#skF_13', B_193, C_194), '#skF_11') | r2_hidden('#skF_6'('#skF_13', B_193, C_194), C_194) | k10_relat_1('#skF_13', B_193)=C_194)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_920])).
% 42.41/30.56  tff(c_3188, plain, (![A_362, B_363, C_364]: (r2_hidden('#skF_5'(A_362, B_363, C_364), k1_relat_1(A_362)) | ~r2_hidden(k1_funct_1(A_362, '#skF_6'(A_362, B_363, C_364)), B_363) | ~r2_hidden('#skF_6'(A_362, B_363, C_364), k1_relat_1(A_362)) | k10_relat_1(A_362, B_363)=C_364 | ~v1_funct_1(A_362) | ~v1_relat_1(A_362))), inference(cnfTransformation, [status(thm)], [f_56])).
% 42.41/30.56  tff(c_3252, plain, (![C_364]: (r2_hidden('#skF_5'('#skF_13', '#skF_12', C_364), k1_relat_1('#skF_13')) | ~r2_hidden('#skF_6'('#skF_13', '#skF_12', C_364), k1_relat_1('#skF_13')) | k10_relat_1('#skF_13', '#skF_12')=C_364 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden('#skF_6'('#skF_13', '#skF_12', C_364), '#skF_11'))), inference(resolution, [status(thm)], [c_72, c_3188])).
% 42.41/30.56  tff(c_3273, plain, (![C_365]: (r2_hidden('#skF_5'('#skF_13', '#skF_12', C_365), '#skF_11') | k10_relat_1('#skF_13', '#skF_12')=C_365 | ~r2_hidden('#skF_6'('#skF_13', '#skF_12', C_365), '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_74, c_3252])).
% 42.41/30.56  tff(c_3291, plain, (r2_hidden('#skF_5'('#skF_13', '#skF_12', '#skF_11'), '#skF_11') | k10_relat_1('#skF_13', '#skF_12')='#skF_11'), inference(resolution, [status(thm)], [c_929, c_3273])).
% 42.41/30.56  tff(c_3295, plain, (k10_relat_1('#skF_13', '#skF_12')='#skF_11'), inference(splitLeft, [status(thm)], [c_3291])).
% 42.41/30.56  tff(c_62, plain, (![B_96, A_95]: (r1_tarski(k9_relat_1(B_96, k10_relat_1(B_96, A_95)), A_95) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_77])).
% 42.41/30.56  tff(c_3356, plain, (r1_tarski(k9_relat_1('#skF_13', '#skF_11'), '#skF_12') | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_3295, c_62])).
% 42.41/30.56  tff(c_3382, plain, (r1_tarski(k2_relat_1('#skF_13'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_500, c_3356])).
% 42.41/30.56  tff(c_89, plain, (![B_107, A_108]: (v1_funct_2(B_107, k1_relat_1(B_107), A_108) | ~r1_tarski(k2_relat_1(B_107), A_108) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_89])).
% 42.41/30.56  tff(c_92, plain, (![A_108]: (v1_funct_2('#skF_13', '#skF_11', A_108) | ~r1_tarski(k2_relat_1('#skF_13'), A_108) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_89])).
% 42.41/30.56  tff(c_94, plain, (![A_108]: (v1_funct_2('#skF_13', '#skF_11', A_108) | ~r1_tarski(k2_relat_1('#skF_13'), A_108))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_92])).
% 42.41/30.56  tff(c_3412, plain, (v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(resolution, [status(thm)], [c_3382, c_94])).
% 42.41/30.56  tff(c_3416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_3412])).
% 42.41/30.56  tff(c_3418, plain, (k10_relat_1('#skF_13', '#skF_12')!='#skF_11'), inference(splitRight, [status(thm)], [c_3291])).
% 42.41/30.56  tff(c_3417, plain, (r2_hidden('#skF_5'('#skF_13', '#skF_12', '#skF_11'), '#skF_11')), inference(splitRight, [status(thm)], [c_3291])).
% 42.41/30.56  tff(c_38, plain, (![A_43, B_50, C_51]: (~r2_hidden('#skF_5'(A_43, B_50, C_51), C_51) | r2_hidden('#skF_6'(A_43, B_50, C_51), C_51) | k10_relat_1(A_43, B_50)=C_51 | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_56])).
% 42.41/30.56  tff(c_32, plain, (![A_43, B_50, C_51]: (~r2_hidden('#skF_5'(A_43, B_50, C_51), C_51) | ~r2_hidden(k1_funct_1(A_43, '#skF_6'(A_43, B_50, C_51)), B_50) | ~r2_hidden('#skF_6'(A_43, B_50, C_51), k1_relat_1(A_43)) | k10_relat_1(A_43, B_50)=C_51 | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_56])).
% 42.41/30.56  tff(c_3420, plain, (~r2_hidden(k1_funct_1('#skF_13', '#skF_6'('#skF_13', '#skF_12', '#skF_11')), '#skF_12') | ~r2_hidden('#skF_6'('#skF_13', '#skF_12', '#skF_11'), k1_relat_1('#skF_13')) | k10_relat_1('#skF_13', '#skF_12')='#skF_11' | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_3417, c_32])).
% 42.41/30.56  tff(c_3423, plain, (~r2_hidden(k1_funct_1('#skF_13', '#skF_6'('#skF_13', '#skF_12', '#skF_11')), '#skF_12') | ~r2_hidden('#skF_6'('#skF_13', '#skF_12', '#skF_11'), '#skF_11') | k10_relat_1('#skF_13', '#skF_12')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_3420])).
% 42.41/30.56  tff(c_3424, plain, (~r2_hidden(k1_funct_1('#skF_13', '#skF_6'('#skF_13', '#skF_12', '#skF_11')), '#skF_12') | ~r2_hidden('#skF_6'('#skF_13', '#skF_12', '#skF_11'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_3418, c_3423])).
% 42.41/30.56  tff(c_3425, plain, (~r2_hidden('#skF_6'('#skF_13', '#skF_12', '#skF_11'), '#skF_11')), inference(splitLeft, [status(thm)], [c_3424])).
% 42.41/30.56  tff(c_3433, plain, (~r2_hidden('#skF_5'('#skF_13', '#skF_12', '#skF_11'), '#skF_11') | k10_relat_1('#skF_13', '#skF_12')='#skF_11' | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_38, c_3425])).
% 42.41/30.56  tff(c_3439, plain, (k10_relat_1('#skF_13', '#skF_12')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_3417, c_3433])).
% 42.41/30.56  tff(c_3441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3418, c_3439])).
% 42.41/30.56  tff(c_3443, plain, (r2_hidden('#skF_6'('#skF_13', '#skF_12', '#skF_11'), '#skF_11')), inference(splitRight, [status(thm)], [c_3424])).
% 42.41/30.56  tff(c_3442, plain, (~r2_hidden(k1_funct_1('#skF_13', '#skF_6'('#skF_13', '#skF_12', '#skF_11')), '#skF_12')), inference(splitRight, [status(thm)], [c_3424])).
% 42.41/30.56  tff(c_3540, plain, (~r2_hidden('#skF_6'('#skF_13', '#skF_12', '#skF_11'), '#skF_11')), inference(resolution, [status(thm)], [c_72, c_3442])).
% 42.41/30.56  tff(c_3547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3443, c_3540])).
% 42.41/30.56  tff(c_3549, plain, (k9_relat_1('#skF_13', '#skF_11')!=k2_relat_1('#skF_13')), inference(splitRight, [status(thm)], [c_363])).
% 42.41/30.56  tff(c_44, plain, (![A_55, D_94]: (r2_hidden(k1_funct_1(A_55, D_94), k2_relat_1(A_55)) | ~r2_hidden(D_94, k1_relat_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_220, plain, (![A_135, E_136, B_137]: (r2_hidden(k1_funct_1(A_135, E_136), k9_relat_1(A_135, B_137)) | ~r2_hidden(E_136, B_137) | ~r2_hidden(E_136, k1_relat_1(A_135)) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_42])).
% 42.41/30.56  tff(c_26, plain, (![D_54, A_43, B_50]: (r2_hidden(D_54, k10_relat_1(A_43, B_50)) | ~r2_hidden(k1_funct_1(A_43, D_54), B_50) | ~r2_hidden(D_54, k1_relat_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_56])).
% 42.41/30.56  tff(c_227, plain, (![E_136, A_135, B_137]: (r2_hidden(E_136, k10_relat_1(A_135, k9_relat_1(A_135, B_137))) | ~r2_hidden(E_136, B_137) | ~r2_hidden(E_136, k1_relat_1(A_135)) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(resolution, [status(thm)], [c_220, c_26])).
% 42.41/30.56  tff(c_110, plain, (![A_118, C_119]: (k1_funct_1(A_118, '#skF_10'(A_118, k2_relat_1(A_118), C_119))=C_119 | ~r2_hidden(C_119, k2_relat_1(A_118)) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_28, plain, (![A_43, D_54, B_50]: (r2_hidden(k1_funct_1(A_43, D_54), B_50) | ~r2_hidden(D_54, k10_relat_1(A_43, B_50)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_56])).
% 42.41/30.56  tff(c_4133, plain, (![C_423, B_424, A_425]: (r2_hidden(C_423, B_424) | ~r2_hidden('#skF_10'(A_425, k2_relat_1(A_425), C_423), k10_relat_1(A_425, B_424)) | ~v1_funct_1(A_425) | ~v1_relat_1(A_425) | ~r2_hidden(C_423, k2_relat_1(A_425)) | ~v1_funct_1(A_425) | ~v1_relat_1(A_425))), inference(superposition, [status(thm), theory('equality')], [c_110, c_28])).
% 42.41/30.56  tff(c_8684, plain, (![C_704, A_705, B_706]: (r2_hidden(C_704, k9_relat_1(A_705, B_706)) | ~r2_hidden(C_704, k2_relat_1(A_705)) | ~r2_hidden('#skF_10'(A_705, k2_relat_1(A_705), C_704), B_706) | ~r2_hidden('#skF_10'(A_705, k2_relat_1(A_705), C_704), k1_relat_1(A_705)) | ~v1_funct_1(A_705) | ~v1_relat_1(A_705))), inference(resolution, [status(thm)], [c_227, c_4133])).
% 42.41/30.56  tff(c_8697, plain, (![C_121]: (r2_hidden(C_121, k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), C_121), k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden(C_121, k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_136, c_8684])).
% 42.41/30.56  tff(c_8710, plain, (![C_707]: (r2_hidden(C_707, k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), C_707), '#skF_11') | ~r2_hidden(C_707, k2_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_8697])).
% 42.41/30.56  tff(c_8715, plain, (![C_708]: (r2_hidden(C_708, k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden(C_708, k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_136, c_8710])).
% 42.41/30.56  tff(c_8771, plain, (![D_709, A_710]: (r2_hidden(D_709, k10_relat_1(A_710, k9_relat_1('#skF_13', '#skF_11'))) | ~r2_hidden(D_709, k1_relat_1(A_710)) | ~v1_funct_1(A_710) | ~v1_relat_1(A_710) | ~r2_hidden(k1_funct_1(A_710, D_709), k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_8715, c_26])).
% 42.41/30.56  tff(c_8808, plain, (![D_94]: (r2_hidden(D_94, k10_relat_1('#skF_13', k9_relat_1('#skF_13', '#skF_11'))) | ~r2_hidden(D_94, k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_44, c_8771])).
% 42.41/30.56  tff(c_8823, plain, (![D_711]: (r2_hidden(D_711, k10_relat_1('#skF_13', k9_relat_1('#skF_13', '#skF_11'))) | ~r2_hidden(D_711, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_8808])).
% 42.41/30.56  tff(c_3552, plain, (![A_371, B_372]: (k1_funct_1(A_371, '#skF_8'(A_371, B_372))='#skF_7'(A_371, B_372) | r2_hidden('#skF_9'(A_371, B_372), B_372) | k2_relat_1(A_371)=B_372 | ~v1_funct_1(A_371) | ~v1_relat_1(A_371))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_3564, plain, (![A_371, B_372, B_50]: (r2_hidden('#skF_7'(A_371, B_372), B_50) | ~r2_hidden('#skF_8'(A_371, B_372), k10_relat_1(A_371, B_50)) | ~v1_funct_1(A_371) | ~v1_relat_1(A_371) | r2_hidden('#skF_9'(A_371, B_372), B_372) | k2_relat_1(A_371)=B_372 | ~v1_funct_1(A_371) | ~v1_relat_1(A_371))), inference(superposition, [status(thm), theory('equality')], [c_3552, c_28])).
% 42.41/30.56  tff(c_8829, plain, (![B_372]: (r2_hidden('#skF_7'('#skF_13', B_372), k9_relat_1('#skF_13', '#skF_11')) | r2_hidden('#skF_9'('#skF_13', B_372), B_372) | k2_relat_1('#skF_13')=B_372 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden('#skF_8'('#skF_13', B_372), '#skF_11'))), inference(resolution, [status(thm)], [c_8823, c_3564])).
% 42.41/30.56  tff(c_9833, plain, (![B_735]: (r2_hidden('#skF_7'('#skF_13', B_735), k9_relat_1('#skF_13', '#skF_11')) | r2_hidden('#skF_9'('#skF_13', B_735), B_735) | k2_relat_1('#skF_13')=B_735 | ~r2_hidden('#skF_8'('#skF_13', B_735), '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_8829])).
% 42.41/30.56  tff(c_56, plain, (![A_55, B_77]: (~r2_hidden('#skF_7'(A_55, B_77), B_77) | r2_hidden('#skF_9'(A_55, B_77), B_77) | k2_relat_1(A_55)=B_77 | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_9851, plain, (~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k9_relat_1('#skF_13', '#skF_11')) | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13') | ~r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11')), inference(resolution, [status(thm)], [c_9833, c_56])).
% 42.41/30.56  tff(c_9924, plain, (r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k9_relat_1('#skF_13', '#skF_11')) | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13') | ~r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_9851])).
% 42.41/30.56  tff(c_9925, plain, (r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_3549, c_9924])).
% 42.41/30.56  tff(c_9942, plain, (~r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11')), inference(splitLeft, [status(thm)], [c_9925])).
% 42.41/30.56  tff(c_60, plain, (![A_55, B_77]: (r2_hidden('#skF_8'(A_55, B_77), k1_relat_1(A_55)) | r2_hidden('#skF_9'(A_55, B_77), B_77) | k2_relat_1(A_55)=B_77 | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_2, plain, (![A_1, E_42, B_24]: (r2_hidden(k1_funct_1(A_1, E_42), k9_relat_1(A_1, B_24)) | ~r2_hidden(E_42, B_24) | ~r2_hidden(E_42, k1_relat_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 42.41/30.56  tff(c_23032, plain, (![A_1238, B_1239, B_1240]: (r2_hidden('#skF_7'(A_1238, B_1239), k9_relat_1(A_1238, B_1240)) | ~r2_hidden('#skF_8'(A_1238, B_1239), B_1240) | ~r2_hidden('#skF_8'(A_1238, B_1239), k1_relat_1(A_1238)) | ~v1_funct_1(A_1238) | ~v1_relat_1(A_1238) | r2_hidden('#skF_9'(A_1238, B_1239), B_1239) | k2_relat_1(A_1238)=B_1239 | ~v1_funct_1(A_1238) | ~v1_relat_1(A_1238))), inference(superposition, [status(thm), theory('equality')], [c_3552, c_2])).
% 42.41/30.56  tff(c_23049, plain, (![A_55, B_77, B_1240]: (r2_hidden('#skF_7'(A_55, B_77), k9_relat_1(A_55, B_1240)) | ~r2_hidden('#skF_8'(A_55, B_77), B_1240) | r2_hidden('#skF_9'(A_55, B_77), B_77) | k2_relat_1(A_55)=B_77 | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(resolution, [status(thm)], [c_60, c_23032])).
% 42.41/30.56  tff(c_8, plain, (![A_1, B_24, D_39]: (r2_hidden('#skF_4'(A_1, B_24, k9_relat_1(A_1, B_24), D_39), k1_relat_1(A_1)) | ~r2_hidden(D_39, k9_relat_1(A_1, B_24)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 42.41/30.56  tff(c_25235, plain, (![D_1315, A_1316, B_1317, B_1318]: (r2_hidden(D_1315, k9_relat_1(A_1316, B_1317)) | ~r2_hidden('#skF_4'(A_1316, B_1318, k9_relat_1(A_1316, B_1318), D_1315), B_1317) | ~r2_hidden('#skF_4'(A_1316, B_1318, k9_relat_1(A_1316, B_1318), D_1315), k1_relat_1(A_1316)) | ~v1_funct_1(A_1316) | ~v1_relat_1(A_1316) | ~r2_hidden(D_1315, k9_relat_1(A_1316, B_1318)) | ~v1_funct_1(A_1316) | ~v1_relat_1(A_1316))), inference(superposition, [status(thm), theory('equality')], [c_309, c_2])).
% 42.41/30.56  tff(c_25305, plain, (![D_1319, A_1320, B_1321]: (r2_hidden(D_1319, k9_relat_1(A_1320, k1_relat_1(A_1320))) | ~r2_hidden('#skF_4'(A_1320, B_1321, k9_relat_1(A_1320, B_1321), D_1319), k1_relat_1(A_1320)) | ~r2_hidden(D_1319, k9_relat_1(A_1320, B_1321)) | ~v1_funct_1(A_1320) | ~v1_relat_1(A_1320))), inference(resolution, [status(thm)], [c_8, c_25235])).
% 42.41/30.56  tff(c_25325, plain, (![D_1322, A_1323, B_1324]: (r2_hidden(D_1322, k9_relat_1(A_1323, k1_relat_1(A_1323))) | ~r2_hidden(D_1322, k9_relat_1(A_1323, B_1324)) | ~v1_funct_1(A_1323) | ~v1_relat_1(A_1323))), inference(resolution, [status(thm)], [c_8, c_25305])).
% 42.41/30.56  tff(c_28048, plain, (![A_1367, B_1368, B_1369]: (r2_hidden('#skF_7'(A_1367, B_1368), k9_relat_1(A_1367, k1_relat_1(A_1367))) | ~r2_hidden('#skF_8'(A_1367, B_1368), B_1369) | r2_hidden('#skF_9'(A_1367, B_1368), B_1368) | k2_relat_1(A_1367)=B_1368 | ~v1_funct_1(A_1367) | ~v1_relat_1(A_1367))), inference(resolution, [status(thm)], [c_23049, c_25325])).
% 42.41/30.56  tff(c_28127, plain, (![A_1370, B_1371]: (r2_hidden('#skF_7'(A_1370, B_1371), k9_relat_1(A_1370, k1_relat_1(A_1370))) | r2_hidden('#skF_9'(A_1370, B_1371), B_1371) | k2_relat_1(A_1370)=B_1371 | ~v1_funct_1(A_1370) | ~v1_relat_1(A_1370))), inference(resolution, [status(thm)], [c_60, c_28048])).
% 42.41/30.56  tff(c_28420, plain, (![A_1374]: (r2_hidden('#skF_9'(A_1374, k9_relat_1(A_1374, k1_relat_1(A_1374))), k9_relat_1(A_1374, k1_relat_1(A_1374))) | k9_relat_1(A_1374, k1_relat_1(A_1374))=k2_relat_1(A_1374) | ~v1_funct_1(A_1374) | ~v1_relat_1(A_1374))), inference(resolution, [status(thm)], [c_28127, c_56])).
% 42.41/30.56  tff(c_163, plain, (![D_129, A_130, B_131]: (r2_hidden(D_129, k10_relat_1(A_130, B_131)) | ~r2_hidden(k1_funct_1(A_130, D_129), B_131) | ~r2_hidden(D_129, k1_relat_1(A_130)) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_56])).
% 42.41/30.56  tff(c_177, plain, (![D_94, A_55]: (r2_hidden(D_94, k10_relat_1(A_55, k2_relat_1(A_55))) | ~r2_hidden(D_94, k1_relat_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(resolution, [status(thm)], [c_44, c_163])).
% 42.41/30.56  tff(c_4596, plain, (![D_475, B_476, A_477, B_478]: (r2_hidden(D_475, B_476) | ~r2_hidden('#skF_4'(A_477, B_478, k9_relat_1(A_477, B_478), D_475), k10_relat_1(A_477, B_476)) | ~v1_funct_1(A_477) | ~v1_relat_1(A_477) | ~r2_hidden(D_475, k9_relat_1(A_477, B_478)) | ~v1_funct_1(A_477) | ~v1_relat_1(A_477))), inference(superposition, [status(thm), theory('equality')], [c_309, c_28])).
% 42.41/30.56  tff(c_4848, plain, (![D_491, A_492, B_493]: (r2_hidden(D_491, k2_relat_1(A_492)) | ~r2_hidden(D_491, k9_relat_1(A_492, B_493)) | ~r2_hidden('#skF_4'(A_492, B_493, k9_relat_1(A_492, B_493), D_491), k1_relat_1(A_492)) | ~v1_funct_1(A_492) | ~v1_relat_1(A_492))), inference(resolution, [status(thm)], [c_177, c_4596])).
% 42.41/30.56  tff(c_4859, plain, (![D_39, A_1, B_24]: (r2_hidden(D_39, k2_relat_1(A_1)) | ~r2_hidden(D_39, k9_relat_1(A_1, B_24)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_8, c_4848])).
% 42.41/30.56  tff(c_28455, plain, (![A_1374]: (r2_hidden('#skF_9'(A_1374, k9_relat_1(A_1374, k1_relat_1(A_1374))), k2_relat_1(A_1374)) | k9_relat_1(A_1374, k1_relat_1(A_1374))=k2_relat_1(A_1374) | ~v1_funct_1(A_1374) | ~v1_relat_1(A_1374))), inference(resolution, [status(thm)], [c_28420, c_4859])).
% 42.41/30.56  tff(c_3917, plain, (![A_403, B_404, D_405]: (r2_hidden('#skF_8'(A_403, B_404), k1_relat_1(A_403)) | k1_funct_1(A_403, D_405)!='#skF_9'(A_403, B_404) | ~r2_hidden(D_405, k1_relat_1(A_403)) | k2_relat_1(A_403)=B_404 | ~v1_funct_1(A_403) | ~v1_relat_1(A_403))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_3923, plain, (![A_55, B_404, C_91]: (r2_hidden('#skF_8'(A_55, B_404), k1_relat_1(A_55)) | C_91!='#skF_9'(A_55, B_404) | ~r2_hidden('#skF_10'(A_55, k2_relat_1(A_55), C_91), k1_relat_1(A_55)) | k2_relat_1(A_55)=B_404 | ~v1_funct_1(A_55) | ~v1_relat_1(A_55) | ~r2_hidden(C_91, k2_relat_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3917])).
% 42.41/30.56  tff(c_47248, plain, (![A_1869, B_1870]: (r2_hidden('#skF_8'(A_1869, B_1870), k1_relat_1(A_1869)) | ~r2_hidden('#skF_10'(A_1869, k2_relat_1(A_1869), '#skF_9'(A_1869, B_1870)), k1_relat_1(A_1869)) | k2_relat_1(A_1869)=B_1870 | ~v1_funct_1(A_1869) | ~v1_relat_1(A_1869) | ~r2_hidden('#skF_9'(A_1869, B_1870), k2_relat_1(A_1869)) | ~v1_funct_1(A_1869) | ~v1_relat_1(A_1869))), inference(reflexivity, [status(thm), theory('equality')], [c_3923])).
% 42.41/30.56  tff(c_47255, plain, (![B_1870]: (r2_hidden('#skF_8'('#skF_13', B_1870), k1_relat_1('#skF_13')) | ~r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), '#skF_9'('#skF_13', B_1870)), '#skF_11') | k2_relat_1('#skF_13')=B_1870 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden('#skF_9'('#skF_13', B_1870), k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_47248])).
% 42.41/30.56  tff(c_47347, plain, (![B_1872]: (r2_hidden('#skF_8'('#skF_13', B_1872), '#skF_11') | ~r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), '#skF_9'('#skF_13', B_1872)), '#skF_11') | k2_relat_1('#skF_13')=B_1872 | ~r2_hidden('#skF_9'('#skF_13', B_1872), k2_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_78, c_76, c_74, c_47255])).
% 42.41/30.56  tff(c_47352, plain, (![B_1873]: (r2_hidden('#skF_8'('#skF_13', B_1873), '#skF_11') | k2_relat_1('#skF_13')=B_1873 | ~r2_hidden('#skF_9'('#skF_13', B_1873), k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_136, c_47347])).
% 42.41/30.56  tff(c_47361, plain, (r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', k1_relat_1('#skF_13'))), '#skF_11') | k9_relat_1('#skF_13', k1_relat_1('#skF_13'))=k2_relat_1('#skF_13') | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_28455, c_47352])).
% 42.41/30.56  tff(c_47422, plain, (r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11') | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_74, c_47361])).
% 42.41/30.56  tff(c_47424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3549, c_9942, c_47422])).
% 42.41/30.56  tff(c_47425, plain, (r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k9_relat_1('#skF_13', '#skF_11'))), inference(splitRight, [status(thm)], [c_9925])).
% 42.41/30.56  tff(c_397, plain, (![A_157, B_158, D_159]: (r2_hidden('#skF_4'(A_157, B_158, k9_relat_1(A_157, B_158), D_159), k1_relat_1(A_157)) | ~r2_hidden(D_159, k9_relat_1(A_157, B_158)) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(cnfTransformation, [status(thm)], [f_42])).
% 42.41/30.56  tff(c_400, plain, (![B_158, D_159]: (r2_hidden('#skF_4'('#skF_13', B_158, k9_relat_1('#skF_13', B_158), D_159), '#skF_11') | ~r2_hidden(D_159, k9_relat_1('#skF_13', B_158)) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_397])).
% 42.41/30.56  tff(c_402, plain, (![B_158, D_159]: (r2_hidden('#skF_4'('#skF_13', B_158, k9_relat_1('#skF_13', B_158), D_159), '#skF_11') | ~r2_hidden(D_159, k9_relat_1('#skF_13', B_158)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_400])).
% 42.41/30.56  tff(c_4858, plain, (![D_491, B_493]: (r2_hidden(D_491, k2_relat_1('#skF_13')) | ~r2_hidden(D_491, k9_relat_1('#skF_13', B_493)) | ~r2_hidden('#skF_4'('#skF_13', B_493, k9_relat_1('#skF_13', B_493), D_491), '#skF_11') | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_4848])).
% 42.41/30.56  tff(c_4968, plain, (![D_497, B_498]: (r2_hidden(D_497, k2_relat_1('#skF_13')) | ~r2_hidden(D_497, k9_relat_1('#skF_13', B_498)) | ~r2_hidden('#skF_4'('#skF_13', B_498, k9_relat_1('#skF_13', B_498), D_497), '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_4858])).
% 42.41/30.56  tff(c_4976, plain, (![D_159, B_158]: (r2_hidden(D_159, k2_relat_1('#skF_13')) | ~r2_hidden(D_159, k9_relat_1('#skF_13', B_158)))), inference(resolution, [status(thm)], [c_402, c_4968])).
% 42.41/30.56  tff(c_47440, plain, (r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_47425, c_4976])).
% 42.41/30.56  tff(c_48, plain, (![A_55, C_91]: (r2_hidden('#skF_10'(A_55, k2_relat_1(A_55), C_91), k1_relat_1(A_55)) | ~r2_hidden(C_91, k2_relat_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_4156, plain, (![A_426, B_427, D_428]: (k1_funct_1(A_426, '#skF_8'(A_426, B_427))='#skF_7'(A_426, B_427) | k1_funct_1(A_426, D_428)!='#skF_9'(A_426, B_427) | ~r2_hidden(D_428, k1_relat_1(A_426)) | k2_relat_1(A_426)=B_427 | ~v1_funct_1(A_426) | ~v1_relat_1(A_426))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_4164, plain, (![A_55, B_427, C_91]: (k1_funct_1(A_55, '#skF_8'(A_55, B_427))='#skF_7'(A_55, B_427) | C_91!='#skF_9'(A_55, B_427) | ~r2_hidden('#skF_10'(A_55, k2_relat_1(A_55), C_91), k1_relat_1(A_55)) | k2_relat_1(A_55)=B_427 | ~v1_funct_1(A_55) | ~v1_relat_1(A_55) | ~r2_hidden(C_91, k2_relat_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_46, c_4156])).
% 42.41/30.56  tff(c_92863, plain, (![A_3250, B_3251]: (k1_funct_1(A_3250, '#skF_8'(A_3250, B_3251))='#skF_7'(A_3250, B_3251) | ~r2_hidden('#skF_10'(A_3250, k2_relat_1(A_3250), '#skF_9'(A_3250, B_3251)), k1_relat_1(A_3250)) | k2_relat_1(A_3250)=B_3251 | ~v1_funct_1(A_3250) | ~v1_relat_1(A_3250) | ~r2_hidden('#skF_9'(A_3250, B_3251), k2_relat_1(A_3250)) | ~v1_funct_1(A_3250) | ~v1_relat_1(A_3250))), inference(reflexivity, [status(thm), theory('equality')], [c_4164])).
% 42.41/30.56  tff(c_92874, plain, (![A_3252, B_3253]: (k1_funct_1(A_3252, '#skF_8'(A_3252, B_3253))='#skF_7'(A_3252, B_3253) | k2_relat_1(A_3252)=B_3253 | ~r2_hidden('#skF_9'(A_3252, B_3253), k2_relat_1(A_3252)) | ~v1_funct_1(A_3252) | ~v1_relat_1(A_3252))), inference(resolution, [status(thm)], [c_48, c_92863])).
% 42.41/30.56  tff(c_92904, plain, (k1_funct_1('#skF_13', '#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')))='#skF_7'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13') | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_47440, c_92874])).
% 42.41/30.56  tff(c_92938, plain, (k1_funct_1('#skF_13', '#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')))='#skF_7'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_92904])).
% 42.41/30.56  tff(c_92939, plain, (k1_funct_1('#skF_13', '#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')))='#skF_7'('#skF_13', k9_relat_1('#skF_13', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_3549, c_92938])).
% 42.41/30.56  tff(c_47426, plain, (r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11')), inference(splitRight, [status(thm)], [c_9925])).
% 42.41/30.56  tff(c_76577, plain, (![D_2894, A_2895, B_2896, B_2897]: (r2_hidden(D_2894, k9_relat_1(A_2895, B_2896)) | ~r2_hidden('#skF_4'(A_2895, B_2897, k9_relat_1(A_2895, B_2897), D_2894), B_2896) | ~r2_hidden('#skF_4'(A_2895, B_2897, k9_relat_1(A_2895, B_2897), D_2894), k1_relat_1(A_2895)) | ~v1_funct_1(A_2895) | ~v1_relat_1(A_2895) | ~r2_hidden(D_2894, k9_relat_1(A_2895, B_2897)) | ~v1_funct_1(A_2895) | ~v1_relat_1(A_2895))), inference(superposition, [status(thm), theory('equality')], [c_309, c_2])).
% 42.41/30.56  tff(c_76666, plain, (![D_2899, A_2900, B_2901]: (r2_hidden(D_2899, k9_relat_1(A_2900, k1_relat_1(A_2900))) | ~r2_hidden('#skF_4'(A_2900, B_2901, k9_relat_1(A_2900, B_2901), D_2899), k1_relat_1(A_2900)) | ~r2_hidden(D_2899, k9_relat_1(A_2900, B_2901)) | ~v1_funct_1(A_2900) | ~v1_relat_1(A_2900))), inference(resolution, [status(thm)], [c_8, c_76577])).
% 42.41/30.56  tff(c_76686, plain, (![D_2902, A_2903, B_2904]: (r2_hidden(D_2902, k9_relat_1(A_2903, k1_relat_1(A_2903))) | ~r2_hidden(D_2902, k9_relat_1(A_2903, B_2904)) | ~v1_funct_1(A_2903) | ~v1_relat_1(A_2903))), inference(resolution, [status(thm)], [c_8, c_76666])).
% 42.41/30.56  tff(c_77092, plain, (![A_2907, E_2908, B_2909]: (r2_hidden(k1_funct_1(A_2907, E_2908), k9_relat_1(A_2907, k1_relat_1(A_2907))) | ~r2_hidden(E_2908, B_2909) | ~r2_hidden(E_2908, k1_relat_1(A_2907)) | ~v1_funct_1(A_2907) | ~v1_relat_1(A_2907))), inference(resolution, [status(thm)], [c_2, c_76686])).
% 42.41/30.56  tff(c_79386, plain, (![A_2940]: (r2_hidden(k1_funct_1(A_2940, '#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11'))), k9_relat_1(A_2940, k1_relat_1(A_2940))) | ~r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k1_relat_1(A_2940)) | ~v1_funct_1(A_2940) | ~v1_relat_1(A_2940))), inference(resolution, [status(thm)], [c_47426, c_77092])).
% 42.41/30.56  tff(c_321, plain, (![D_151, B_50, A_149, B_150]: (r2_hidden(D_151, B_50) | ~r2_hidden('#skF_4'(A_149, B_150, k9_relat_1(A_149, B_150), D_151), k10_relat_1(A_149, B_50)) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149) | ~r2_hidden(D_151, k9_relat_1(A_149, B_150)) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(superposition, [status(thm), theory('equality')], [c_309, c_28])).
% 42.41/30.56  tff(c_8848, plain, (![D_151, B_150]: (r2_hidden(D_151, k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden(D_151, k9_relat_1('#skF_13', B_150)) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden('#skF_4'('#skF_13', B_150, k9_relat_1('#skF_13', B_150), D_151), '#skF_11'))), inference(resolution, [status(thm)], [c_8823, c_321])).
% 42.41/30.56  tff(c_8933, plain, (![D_716, B_717]: (r2_hidden(D_716, k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden(D_716, k9_relat_1('#skF_13', B_717)) | ~r2_hidden('#skF_4'('#skF_13', B_717, k9_relat_1('#skF_13', B_717), D_716), '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_8848])).
% 42.41/30.56  tff(c_8941, plain, (![D_159, B_158]: (r2_hidden(D_159, k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden(D_159, k9_relat_1('#skF_13', B_158)))), inference(resolution, [status(thm)], [c_402, c_8933])).
% 42.41/30.56  tff(c_79393, plain, (r2_hidden(k1_funct_1('#skF_13', '#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11'))), k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_79386, c_8941])).
% 42.41/30.56  tff(c_79419, plain, (r2_hidden(k1_funct_1('#skF_13', '#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11'))), k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_47426, c_74, c_79393])).
% 42.41/30.56  tff(c_92961, plain, (r2_hidden('#skF_7'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_92939, c_79419])).
% 42.41/30.56  tff(c_50, plain, (![A_55, B_77, D_90]: (~r2_hidden('#skF_7'(A_55, B_77), B_77) | k1_funct_1(A_55, D_90)!='#skF_9'(A_55, B_77) | ~r2_hidden(D_90, k1_relat_1(A_55)) | k2_relat_1(A_55)=B_77 | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_93184, plain, (![D_90]: (k1_funct_1('#skF_13', D_90)!='#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden(D_90, k1_relat_1('#skF_13')) | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13') | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_92961, c_50])).
% 42.41/30.56  tff(c_93209, plain, (![D_90]: (k1_funct_1('#skF_13', D_90)!='#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden(D_90, '#skF_11') | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_93184])).
% 42.41/30.56  tff(c_93445, plain, (![D_3259]: (k1_funct_1('#skF_13', D_3259)!='#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden(D_3259, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_3549, c_93209])).
% 42.41/30.56  tff(c_93466, plain, (![C_91]: (C_91!='#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), C_91), '#skF_11') | ~r2_hidden(C_91, k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_93445])).
% 42.41/30.56  tff(c_93960, plain, (![C_3268]: (C_3268!='#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), C_3268), '#skF_11') | ~r2_hidden(C_3268, k2_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_93466])).
% 42.41/30.56  tff(c_93965, plain, (~r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_136, c_93960])).
% 42.41/30.56  tff(c_93967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93965, c_47440])).
% 42.41/30.56  tff(c_93968, plain, (~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12')))), inference(splitRight, [status(thm)], [c_80])).
% 42.41/30.56  tff(c_93996, plain, (~r1_tarski(k2_relat_1('#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_93992, c_93968])).
% 42.41/30.56  tff(c_94066, plain, (![A_3299, B_3300]: (r2_hidden('#skF_8'(A_3299, B_3300), k1_relat_1(A_3299)) | r2_hidden('#skF_9'(A_3299, B_3300), B_3300) | k2_relat_1(A_3299)=B_3300 | ~v1_funct_1(A_3299) | ~v1_relat_1(A_3299))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_94079, plain, (![B_3300]: (r2_hidden('#skF_8'('#skF_13', B_3300), '#skF_11') | r2_hidden('#skF_9'('#skF_13', B_3300), B_3300) | k2_relat_1('#skF_13')=B_3300 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_94066])).
% 42.41/30.56  tff(c_94083, plain, (![B_3300]: (r2_hidden('#skF_8'('#skF_13', B_3300), '#skF_11') | r2_hidden('#skF_9'('#skF_13', B_3300), B_3300) | k2_relat_1('#skF_13')=B_3300)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_94079])).
% 42.41/30.56  tff(c_94196, plain, (![A_3316, B_3317, D_3318]: (k1_funct_1(A_3316, '#skF_4'(A_3316, B_3317, k9_relat_1(A_3316, B_3317), D_3318))=D_3318 | ~r2_hidden(D_3318, k9_relat_1(A_3316, B_3317)) | ~v1_funct_1(A_3316) | ~v1_relat_1(A_3316))), inference(cnfTransformation, [status(thm)], [f_42])).
% 42.41/30.56  tff(c_94215, plain, (![D_3318, B_3317]: (r2_hidden(D_3318, '#skF_12') | ~r2_hidden('#skF_4'('#skF_13', B_3317, k9_relat_1('#skF_13', B_3317), D_3318), '#skF_11') | ~r2_hidden(D_3318, k9_relat_1('#skF_13', B_3317)) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_94196, c_72])).
% 42.41/30.56  tff(c_94223, plain, (![D_3319, B_3320]: (r2_hidden(D_3319, '#skF_12') | ~r2_hidden('#skF_4'('#skF_13', B_3320, k9_relat_1('#skF_13', B_3320), D_3319), '#skF_11') | ~r2_hidden(D_3319, k9_relat_1('#skF_13', B_3320)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_94215])).
% 42.41/30.56  tff(c_94227, plain, (![D_39]: (r2_hidden(D_39, '#skF_12') | ~r2_hidden(D_39, k9_relat_1('#skF_13', '#skF_11')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_6, c_94223])).
% 42.41/30.56  tff(c_94231, plain, (![D_3321]: (r2_hidden(D_3321, '#skF_12') | ~r2_hidden(D_3321, k9_relat_1('#skF_13', '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_94227])).
% 42.41/30.56  tff(c_94253, plain, (r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_12') | r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11') | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_94083, c_94231])).
% 42.41/30.56  tff(c_94351, plain, (k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13')), inference(splitLeft, [status(thm)], [c_94253])).
% 42.41/30.56  tff(c_94849, plain, (![A_3366, B_3367, C_3368]: (r2_hidden('#skF_5'(A_3366, B_3367, C_3368), k1_relat_1(A_3366)) | r2_hidden('#skF_6'(A_3366, B_3367, C_3368), C_3368) | k10_relat_1(A_3366, B_3367)=C_3368 | ~v1_funct_1(A_3366) | ~v1_relat_1(A_3366))), inference(cnfTransformation, [status(thm)], [f_56])).
% 42.41/30.56  tff(c_94879, plain, (![B_3367, C_3368]: (r2_hidden('#skF_5'('#skF_13', B_3367, C_3368), '#skF_11') | r2_hidden('#skF_6'('#skF_13', B_3367, C_3368), C_3368) | k10_relat_1('#skF_13', B_3367)=C_3368 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_94849])).
% 42.41/30.56  tff(c_94888, plain, (![B_3367, C_3368]: (r2_hidden('#skF_5'('#skF_13', B_3367, C_3368), '#skF_11') | r2_hidden('#skF_6'('#skF_13', B_3367, C_3368), C_3368) | k10_relat_1('#skF_13', B_3367)=C_3368)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_94879])).
% 42.41/30.56  tff(c_97045, plain, (![A_3527, B_3528, C_3529]: (r2_hidden('#skF_5'(A_3527, B_3528, C_3529), k1_relat_1(A_3527)) | ~r2_hidden(k1_funct_1(A_3527, '#skF_6'(A_3527, B_3528, C_3529)), B_3528) | ~r2_hidden('#skF_6'(A_3527, B_3528, C_3529), k1_relat_1(A_3527)) | k10_relat_1(A_3527, B_3528)=C_3529 | ~v1_funct_1(A_3527) | ~v1_relat_1(A_3527))), inference(cnfTransformation, [status(thm)], [f_56])).
% 42.41/30.56  tff(c_97109, plain, (![C_3529]: (r2_hidden('#skF_5'('#skF_13', '#skF_12', C_3529), k1_relat_1('#skF_13')) | ~r2_hidden('#skF_6'('#skF_13', '#skF_12', C_3529), k1_relat_1('#skF_13')) | k10_relat_1('#skF_13', '#skF_12')=C_3529 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden('#skF_6'('#skF_13', '#skF_12', C_3529), '#skF_11'))), inference(resolution, [status(thm)], [c_72, c_97045])).
% 42.41/30.56  tff(c_97130, plain, (![C_3530]: (r2_hidden('#skF_5'('#skF_13', '#skF_12', C_3530), '#skF_11') | k10_relat_1('#skF_13', '#skF_12')=C_3530 | ~r2_hidden('#skF_6'('#skF_13', '#skF_12', C_3530), '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_74, c_97109])).
% 42.41/30.56  tff(c_97148, plain, (r2_hidden('#skF_5'('#skF_13', '#skF_12', '#skF_11'), '#skF_11') | k10_relat_1('#skF_13', '#skF_12')='#skF_11'), inference(resolution, [status(thm)], [c_94888, c_97130])).
% 42.41/30.56  tff(c_97152, plain, (k10_relat_1('#skF_13', '#skF_12')='#skF_11'), inference(splitLeft, [status(thm)], [c_97148])).
% 42.41/30.56  tff(c_97213, plain, (r1_tarski(k9_relat_1('#skF_13', '#skF_11'), '#skF_12') | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_97152, c_62])).
% 42.41/30.56  tff(c_97239, plain, (r1_tarski(k2_relat_1('#skF_13'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_94351, c_97213])).
% 42.41/30.56  tff(c_97241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93996, c_97239])).
% 42.41/30.56  tff(c_97243, plain, (k10_relat_1('#skF_13', '#skF_12')!='#skF_11'), inference(splitRight, [status(thm)], [c_97148])).
% 42.41/30.56  tff(c_97242, plain, (r2_hidden('#skF_5'('#skF_13', '#skF_12', '#skF_11'), '#skF_11')), inference(splitRight, [status(thm)], [c_97148])).
% 42.41/30.56  tff(c_97246, plain, (~r2_hidden(k1_funct_1('#skF_13', '#skF_6'('#skF_13', '#skF_12', '#skF_11')), '#skF_12') | ~r2_hidden('#skF_6'('#skF_13', '#skF_12', '#skF_11'), k1_relat_1('#skF_13')) | k10_relat_1('#skF_13', '#skF_12')='#skF_11' | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_97242, c_32])).
% 42.41/30.56  tff(c_97249, plain, (~r2_hidden(k1_funct_1('#skF_13', '#skF_6'('#skF_13', '#skF_12', '#skF_11')), '#skF_12') | ~r2_hidden('#skF_6'('#skF_13', '#skF_12', '#skF_11'), '#skF_11') | k10_relat_1('#skF_13', '#skF_12')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_97246])).
% 42.41/30.56  tff(c_97250, plain, (~r2_hidden(k1_funct_1('#skF_13', '#skF_6'('#skF_13', '#skF_12', '#skF_11')), '#skF_12') | ~r2_hidden('#skF_6'('#skF_13', '#skF_12', '#skF_11'), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_97243, c_97249])).
% 42.41/30.56  tff(c_97251, plain, (~r2_hidden('#skF_6'('#skF_13', '#skF_12', '#skF_11'), '#skF_11')), inference(splitLeft, [status(thm)], [c_97250])).
% 42.41/30.56  tff(c_97259, plain, (~r2_hidden('#skF_5'('#skF_13', '#skF_12', '#skF_11'), '#skF_11') | k10_relat_1('#skF_13', '#skF_12')='#skF_11' | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_38, c_97251])).
% 42.41/30.56  tff(c_97265, plain, (k10_relat_1('#skF_13', '#skF_12')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_97242, c_97259])).
% 42.41/30.56  tff(c_97267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97243, c_97265])).
% 42.41/30.56  tff(c_97269, plain, (r2_hidden('#skF_6'('#skF_13', '#skF_12', '#skF_11'), '#skF_11')), inference(splitRight, [status(thm)], [c_97250])).
% 42.41/30.56  tff(c_97268, plain, (~r2_hidden(k1_funct_1('#skF_13', '#skF_6'('#skF_13', '#skF_12', '#skF_11')), '#skF_12')), inference(splitRight, [status(thm)], [c_97250])).
% 42.41/30.56  tff(c_97366, plain, (~r2_hidden('#skF_6'('#skF_13', '#skF_12', '#skF_11'), '#skF_11')), inference(resolution, [status(thm)], [c_72, c_97268])).
% 42.41/30.56  tff(c_97373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97269, c_97366])).
% 42.41/30.56  tff(c_97375, plain, (k9_relat_1('#skF_13', '#skF_11')!=k2_relat_1('#skF_13')), inference(splitRight, [status(thm)], [c_94253])).
% 42.41/30.56  tff(c_94158, plain, (![A_3308, E_3309, B_3310]: (r2_hidden(k1_funct_1(A_3308, E_3309), k9_relat_1(A_3308, B_3310)) | ~r2_hidden(E_3309, B_3310) | ~r2_hidden(E_3309, k1_relat_1(A_3308)) | ~v1_funct_1(A_3308) | ~v1_relat_1(A_3308))), inference(cnfTransformation, [status(thm)], [f_42])).
% 42.41/30.56  tff(c_94165, plain, (![E_3309, A_3308, B_3310]: (r2_hidden(E_3309, k10_relat_1(A_3308, k9_relat_1(A_3308, B_3310))) | ~r2_hidden(E_3309, B_3310) | ~r2_hidden(E_3309, k1_relat_1(A_3308)) | ~v1_funct_1(A_3308) | ~v1_relat_1(A_3308))), inference(resolution, [status(thm)], [c_94158, c_26])).
% 42.41/30.56  tff(c_93997, plain, (![A_3285, C_3286]: (k1_funct_1(A_3285, '#skF_10'(A_3285, k2_relat_1(A_3285), C_3286))=C_3286 | ~r2_hidden(C_3286, k2_relat_1(A_3285)) | ~v1_funct_1(A_3285) | ~v1_relat_1(A_3285))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_97985, plain, (![C_3591, B_3592, A_3593]: (r2_hidden(C_3591, B_3592) | ~r2_hidden('#skF_10'(A_3593, k2_relat_1(A_3593), C_3591), k10_relat_1(A_3593, B_3592)) | ~v1_funct_1(A_3593) | ~v1_relat_1(A_3593) | ~r2_hidden(C_3591, k2_relat_1(A_3593)) | ~v1_funct_1(A_3593) | ~v1_relat_1(A_3593))), inference(superposition, [status(thm), theory('equality')], [c_93997, c_28])).
% 42.41/30.56  tff(c_102505, plain, (![C_3878, A_3879, B_3880]: (r2_hidden(C_3878, k9_relat_1(A_3879, B_3880)) | ~r2_hidden(C_3878, k2_relat_1(A_3879)) | ~r2_hidden('#skF_10'(A_3879, k2_relat_1(A_3879), C_3878), B_3880) | ~r2_hidden('#skF_10'(A_3879, k2_relat_1(A_3879), C_3878), k1_relat_1(A_3879)) | ~v1_funct_1(A_3879) | ~v1_relat_1(A_3879))), inference(resolution, [status(thm)], [c_94165, c_97985])).
% 42.41/30.56  tff(c_102518, plain, (![C_3289]: (r2_hidden(C_3289, k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), C_3289), k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden(C_3289, k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_94024, c_102505])).
% 42.41/30.56  tff(c_110194, plain, (![C_4193]: (r2_hidden(C_4193, k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), C_4193), '#skF_11') | ~r2_hidden(C_4193, k2_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_102518])).
% 42.41/30.56  tff(c_110199, plain, (![C_4194]: (r2_hidden(C_4194, k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden(C_4194, k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_94024, c_110194])).
% 42.41/30.56  tff(c_110255, plain, (![D_4195, A_4196]: (r2_hidden(D_4195, k10_relat_1(A_4196, k9_relat_1('#skF_13', '#skF_11'))) | ~r2_hidden(D_4195, k1_relat_1(A_4196)) | ~v1_funct_1(A_4196) | ~v1_relat_1(A_4196) | ~r2_hidden(k1_funct_1(A_4196, D_4195), k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_110199, c_26])).
% 42.41/30.56  tff(c_110292, plain, (![D_94]: (r2_hidden(D_94, k10_relat_1('#skF_13', k9_relat_1('#skF_13', '#skF_11'))) | ~r2_hidden(D_94, k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_44, c_110255])).
% 42.41/30.56  tff(c_110307, plain, (![D_4197]: (r2_hidden(D_4197, k10_relat_1('#skF_13', k9_relat_1('#skF_13', '#skF_11'))) | ~r2_hidden(D_4197, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_110292])).
% 42.41/30.56  tff(c_97476, plain, (![A_3545, B_3546]: (k1_funct_1(A_3545, '#skF_8'(A_3545, B_3546))='#skF_7'(A_3545, B_3546) | r2_hidden('#skF_9'(A_3545, B_3546), B_3546) | k2_relat_1(A_3545)=B_3546 | ~v1_funct_1(A_3545) | ~v1_relat_1(A_3545))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_97488, plain, (![A_3545, B_3546, B_50]: (r2_hidden('#skF_7'(A_3545, B_3546), B_50) | ~r2_hidden('#skF_8'(A_3545, B_3546), k10_relat_1(A_3545, B_50)) | ~v1_funct_1(A_3545) | ~v1_relat_1(A_3545) | r2_hidden('#skF_9'(A_3545, B_3546), B_3546) | k2_relat_1(A_3545)=B_3546 | ~v1_funct_1(A_3545) | ~v1_relat_1(A_3545))), inference(superposition, [status(thm), theory('equality')], [c_97476, c_28])).
% 42.41/30.56  tff(c_110313, plain, (![B_3546]: (r2_hidden('#skF_7'('#skF_13', B_3546), k9_relat_1('#skF_13', '#skF_11')) | r2_hidden('#skF_9'('#skF_13', B_3546), B_3546) | k2_relat_1('#skF_13')=B_3546 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden('#skF_8'('#skF_13', B_3546), '#skF_11'))), inference(resolution, [status(thm)], [c_110307, c_97488])).
% 42.41/30.56  tff(c_111402, plain, (![B_4220]: (r2_hidden('#skF_7'('#skF_13', B_4220), k9_relat_1('#skF_13', '#skF_11')) | r2_hidden('#skF_9'('#skF_13', B_4220), B_4220) | k2_relat_1('#skF_13')=B_4220 | ~r2_hidden('#skF_8'('#skF_13', B_4220), '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_110313])).
% 42.41/30.56  tff(c_111420, plain, (~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k9_relat_1('#skF_13', '#skF_11')) | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13') | ~r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11')), inference(resolution, [status(thm)], [c_111402, c_56])).
% 42.41/30.56  tff(c_111493, plain, (r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k9_relat_1('#skF_13', '#skF_11')) | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13') | ~r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_111420])).
% 42.41/30.56  tff(c_111494, plain, (r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_97375, c_111493])).
% 42.41/30.56  tff(c_111511, plain, (~r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11')), inference(splitLeft, [status(thm)], [c_111494])).
% 42.41/30.56  tff(c_115188, plain, (![A_4372, B_4373, B_4374]: (r2_hidden('#skF_7'(A_4372, B_4373), k9_relat_1(A_4372, B_4374)) | ~r2_hidden('#skF_8'(A_4372, B_4373), B_4374) | ~r2_hidden('#skF_8'(A_4372, B_4373), k1_relat_1(A_4372)) | ~v1_funct_1(A_4372) | ~v1_relat_1(A_4372) | r2_hidden('#skF_9'(A_4372, B_4373), B_4373) | k2_relat_1(A_4372)=B_4373 | ~v1_funct_1(A_4372) | ~v1_relat_1(A_4372))), inference(superposition, [status(thm), theory('equality')], [c_97476, c_2])).
% 42.41/30.56  tff(c_115205, plain, (![A_55, B_77, B_4374]: (r2_hidden('#skF_7'(A_55, B_77), k9_relat_1(A_55, B_4374)) | ~r2_hidden('#skF_8'(A_55, B_77), B_4374) | r2_hidden('#skF_9'(A_55, B_77), B_77) | k2_relat_1(A_55)=B_77 | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(resolution, [status(thm)], [c_60, c_115188])).
% 42.41/30.56  tff(c_117795, plain, (![D_4465, A_4466, B_4467, B_4468]: (r2_hidden(D_4465, k9_relat_1(A_4466, B_4467)) | ~r2_hidden('#skF_4'(A_4466, B_4468, k9_relat_1(A_4466, B_4468), D_4465), B_4467) | ~r2_hidden('#skF_4'(A_4466, B_4468, k9_relat_1(A_4466, B_4468), D_4465), k1_relat_1(A_4466)) | ~v1_funct_1(A_4466) | ~v1_relat_1(A_4466) | ~r2_hidden(D_4465, k9_relat_1(A_4466, B_4468)) | ~v1_funct_1(A_4466) | ~v1_relat_1(A_4466))), inference(superposition, [status(thm), theory('equality')], [c_94196, c_2])).
% 42.41/30.56  tff(c_117861, plain, (![D_4469, A_4470, B_4471]: (r2_hidden(D_4469, k9_relat_1(A_4470, k1_relat_1(A_4470))) | ~r2_hidden('#skF_4'(A_4470, B_4471, k9_relat_1(A_4470, B_4471), D_4469), k1_relat_1(A_4470)) | ~r2_hidden(D_4469, k9_relat_1(A_4470, B_4471)) | ~v1_funct_1(A_4470) | ~v1_relat_1(A_4470))), inference(resolution, [status(thm)], [c_8, c_117795])).
% 42.41/30.56  tff(c_117881, plain, (![D_4472, A_4473, B_4474]: (r2_hidden(D_4472, k9_relat_1(A_4473, k1_relat_1(A_4473))) | ~r2_hidden(D_4472, k9_relat_1(A_4473, B_4474)) | ~v1_funct_1(A_4473) | ~v1_relat_1(A_4473))), inference(resolution, [status(thm)], [c_8, c_117861])).
% 42.41/30.56  tff(c_120956, plain, (![A_4523, B_4524, B_4525]: (r2_hidden('#skF_7'(A_4523, B_4524), k9_relat_1(A_4523, k1_relat_1(A_4523))) | ~r2_hidden('#skF_8'(A_4523, B_4524), B_4525) | r2_hidden('#skF_9'(A_4523, B_4524), B_4524) | k2_relat_1(A_4523)=B_4524 | ~v1_funct_1(A_4523) | ~v1_relat_1(A_4523))), inference(resolution, [status(thm)], [c_115205, c_117881])).
% 42.41/30.56  tff(c_121037, plain, (![A_4526, B_4527]: (r2_hidden('#skF_7'(A_4526, B_4527), k9_relat_1(A_4526, k1_relat_1(A_4526))) | r2_hidden('#skF_9'(A_4526, B_4527), B_4527) | k2_relat_1(A_4526)=B_4527 | ~v1_funct_1(A_4526) | ~v1_relat_1(A_4526))), inference(resolution, [status(thm)], [c_60, c_120956])).
% 42.41/30.56  tff(c_121181, plain, (![A_4528]: (r2_hidden('#skF_9'(A_4528, k9_relat_1(A_4528, k1_relat_1(A_4528))), k9_relat_1(A_4528, k1_relat_1(A_4528))) | k9_relat_1(A_4528, k1_relat_1(A_4528))=k2_relat_1(A_4528) | ~v1_funct_1(A_4528) | ~v1_relat_1(A_4528))), inference(resolution, [status(thm)], [c_121037, c_56])).
% 42.41/30.56  tff(c_98361, plain, (![D_3638, A_3639, B_3640]: (r2_hidden(D_3638, k2_relat_1(A_3639)) | ~r2_hidden('#skF_4'(A_3639, B_3640, k9_relat_1(A_3639, B_3640), D_3638), k1_relat_1(A_3639)) | ~v1_funct_1(A_3639) | ~v1_relat_1(A_3639) | ~r2_hidden(D_3638, k9_relat_1(A_3639, B_3640)) | ~v1_funct_1(A_3639) | ~v1_relat_1(A_3639))), inference(superposition, [status(thm), theory('equality')], [c_94196, c_44])).
% 42.41/30.56  tff(c_98372, plain, (![D_39, A_1, B_24]: (r2_hidden(D_39, k2_relat_1(A_1)) | ~r2_hidden(D_39, k9_relat_1(A_1, B_24)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_8, c_98361])).
% 42.41/30.56  tff(c_121216, plain, (![A_4528]: (r2_hidden('#skF_9'(A_4528, k9_relat_1(A_4528, k1_relat_1(A_4528))), k2_relat_1(A_4528)) | k9_relat_1(A_4528, k1_relat_1(A_4528))=k2_relat_1(A_4528) | ~v1_funct_1(A_4528) | ~v1_relat_1(A_4528))), inference(resolution, [status(thm)], [c_121181, c_98372])).
% 42.41/30.56  tff(c_97769, plain, (![A_3571, B_3572, D_3573]: (r2_hidden('#skF_8'(A_3571, B_3572), k1_relat_1(A_3571)) | k1_funct_1(A_3571, D_3573)!='#skF_9'(A_3571, B_3572) | ~r2_hidden(D_3573, k1_relat_1(A_3571)) | k2_relat_1(A_3571)=B_3572 | ~v1_funct_1(A_3571) | ~v1_relat_1(A_3571))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_97775, plain, (![A_55, B_3572, C_91]: (r2_hidden('#skF_8'(A_55, B_3572), k1_relat_1(A_55)) | C_91!='#skF_9'(A_55, B_3572) | ~r2_hidden('#skF_10'(A_55, k2_relat_1(A_55), C_91), k1_relat_1(A_55)) | k2_relat_1(A_55)=B_3572 | ~v1_funct_1(A_55) | ~v1_relat_1(A_55) | ~r2_hidden(C_91, k2_relat_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_46, c_97769])).
% 42.41/30.56  tff(c_129877, plain, (![A_4753, B_4754]: (r2_hidden('#skF_8'(A_4753, B_4754), k1_relat_1(A_4753)) | ~r2_hidden('#skF_10'(A_4753, k2_relat_1(A_4753), '#skF_9'(A_4753, B_4754)), k1_relat_1(A_4753)) | k2_relat_1(A_4753)=B_4754 | ~v1_funct_1(A_4753) | ~v1_relat_1(A_4753) | ~r2_hidden('#skF_9'(A_4753, B_4754), k2_relat_1(A_4753)) | ~v1_funct_1(A_4753) | ~v1_relat_1(A_4753))), inference(reflexivity, [status(thm), theory('equality')], [c_97775])).
% 42.41/30.56  tff(c_129888, plain, (![A_4755, B_4756]: (r2_hidden('#skF_8'(A_4755, B_4756), k1_relat_1(A_4755)) | k2_relat_1(A_4755)=B_4756 | ~r2_hidden('#skF_9'(A_4755, B_4756), k2_relat_1(A_4755)) | ~v1_funct_1(A_4755) | ~v1_relat_1(A_4755))), inference(resolution, [status(thm)], [c_48, c_129877])).
% 42.41/30.56  tff(c_129911, plain, (![B_4756]: (r2_hidden('#skF_8'('#skF_13', B_4756), '#skF_11') | k2_relat_1('#skF_13')=B_4756 | ~r2_hidden('#skF_9'('#skF_13', B_4756), k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_129888])).
% 42.41/30.56  tff(c_129930, plain, (![B_4757]: (r2_hidden('#skF_8'('#skF_13', B_4757), '#skF_11') | k2_relat_1('#skF_13')=B_4757 | ~r2_hidden('#skF_9'('#skF_13', B_4757), k2_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_129911])).
% 42.41/30.56  tff(c_129936, plain, (r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', k1_relat_1('#skF_13'))), '#skF_11') | k9_relat_1('#skF_13', k1_relat_1('#skF_13'))=k2_relat_1('#skF_13') | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_121216, c_129930])).
% 42.41/30.56  tff(c_129994, plain, (r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11') | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_74, c_129936])).
% 42.41/30.56  tff(c_129996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97375, c_111511, c_129994])).
% 42.41/30.56  tff(c_129997, plain, (r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k9_relat_1('#skF_13', '#skF_11'))), inference(splitRight, [status(thm)], [c_111494])).
% 42.41/30.56  tff(c_94284, plain, (![A_3324, B_3325, D_3326]: (r2_hidden('#skF_4'(A_3324, B_3325, k9_relat_1(A_3324, B_3325), D_3326), k1_relat_1(A_3324)) | ~r2_hidden(D_3326, k9_relat_1(A_3324, B_3325)) | ~v1_funct_1(A_3324) | ~v1_relat_1(A_3324))), inference(cnfTransformation, [status(thm)], [f_42])).
% 42.41/30.56  tff(c_94287, plain, (![B_3325, D_3326]: (r2_hidden('#skF_4'('#skF_13', B_3325, k9_relat_1('#skF_13', B_3325), D_3326), '#skF_11') | ~r2_hidden(D_3326, k9_relat_1('#skF_13', B_3325)) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_94284])).
% 42.41/30.56  tff(c_94289, plain, (![B_3325, D_3326]: (r2_hidden('#skF_4'('#skF_13', B_3325, k9_relat_1('#skF_13', B_3325), D_3326), '#skF_11') | ~r2_hidden(D_3326, k9_relat_1('#skF_13', B_3325)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_94287])).
% 42.41/30.56  tff(c_98371, plain, (![D_3638, B_3640]: (r2_hidden(D_3638, k2_relat_1('#skF_13')) | ~r2_hidden('#skF_4'('#skF_13', B_3640, k9_relat_1('#skF_13', B_3640), D_3638), '#skF_11') | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden(D_3638, k9_relat_1('#skF_13', B_3640)) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_98361])).
% 42.41/30.56  tff(c_98481, plain, (![D_3644, B_3645]: (r2_hidden(D_3644, k2_relat_1('#skF_13')) | ~r2_hidden('#skF_4'('#skF_13', B_3645, k9_relat_1('#skF_13', B_3645), D_3644), '#skF_11') | ~r2_hidden(D_3644, k9_relat_1('#skF_13', B_3645)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_78, c_76, c_98371])).
% 42.41/30.56  tff(c_98489, plain, (![D_3326, B_3325]: (r2_hidden(D_3326, k2_relat_1('#skF_13')) | ~r2_hidden(D_3326, k9_relat_1('#skF_13', B_3325)))), inference(resolution, [status(thm)], [c_94289, c_98481])).
% 42.41/30.56  tff(c_130030, plain, (r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_129997, c_98489])).
% 42.41/30.56  tff(c_98008, plain, (![A_3594, B_3595, D_3596]: (k1_funct_1(A_3594, '#skF_8'(A_3594, B_3595))='#skF_7'(A_3594, B_3595) | k1_funct_1(A_3594, D_3596)!='#skF_9'(A_3594, B_3595) | ~r2_hidden(D_3596, k1_relat_1(A_3594)) | k2_relat_1(A_3594)=B_3595 | ~v1_funct_1(A_3594) | ~v1_relat_1(A_3594))), inference(cnfTransformation, [status(thm)], [f_71])).
% 42.41/30.56  tff(c_98016, plain, (![A_55, B_3595, C_91]: (k1_funct_1(A_55, '#skF_8'(A_55, B_3595))='#skF_7'(A_55, B_3595) | C_91!='#skF_9'(A_55, B_3595) | ~r2_hidden('#skF_10'(A_55, k2_relat_1(A_55), C_91), k1_relat_1(A_55)) | k2_relat_1(A_55)=B_3595 | ~v1_funct_1(A_55) | ~v1_relat_1(A_55) | ~r2_hidden(C_91, k2_relat_1(A_55)) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_46, c_98008])).
% 42.41/30.56  tff(c_153756, plain, (![A_5369, B_5370]: (k1_funct_1(A_5369, '#skF_8'(A_5369, B_5370))='#skF_7'(A_5369, B_5370) | ~r2_hidden('#skF_10'(A_5369, k2_relat_1(A_5369), '#skF_9'(A_5369, B_5370)), k1_relat_1(A_5369)) | k2_relat_1(A_5369)=B_5370 | ~v1_funct_1(A_5369) | ~v1_relat_1(A_5369) | ~r2_hidden('#skF_9'(A_5369, B_5370), k2_relat_1(A_5369)) | ~v1_funct_1(A_5369) | ~v1_relat_1(A_5369))), inference(reflexivity, [status(thm), theory('equality')], [c_98016])).
% 42.41/30.56  tff(c_153767, plain, (![A_5371, B_5372]: (k1_funct_1(A_5371, '#skF_8'(A_5371, B_5372))='#skF_7'(A_5371, B_5372) | k2_relat_1(A_5371)=B_5372 | ~r2_hidden('#skF_9'(A_5371, B_5372), k2_relat_1(A_5371)) | ~v1_funct_1(A_5371) | ~v1_relat_1(A_5371))), inference(resolution, [status(thm)], [c_48, c_153756])).
% 42.41/30.56  tff(c_153797, plain, (k1_funct_1('#skF_13', '#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')))='#skF_7'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13') | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_130030, c_153767])).
% 42.41/30.56  tff(c_153831, plain, (k1_funct_1('#skF_13', '#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')))='#skF_7'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_153797])).
% 42.41/30.56  tff(c_153832, plain, (k1_funct_1('#skF_13', '#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')))='#skF_7'('#skF_13', k9_relat_1('#skF_13', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_97375, c_153831])).
% 42.41/30.56  tff(c_129998, plain, (r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), '#skF_11')), inference(splitRight, [status(thm)], [c_111494])).
% 42.41/30.56  tff(c_136491, plain, (![D_5019, A_5020, B_5021, B_5022]: (r2_hidden(D_5019, k9_relat_1(A_5020, B_5021)) | ~r2_hidden('#skF_4'(A_5020, B_5022, k9_relat_1(A_5020, B_5022), D_5019), B_5021) | ~r2_hidden('#skF_4'(A_5020, B_5022, k9_relat_1(A_5020, B_5022), D_5019), k1_relat_1(A_5020)) | ~v1_funct_1(A_5020) | ~v1_relat_1(A_5020) | ~r2_hidden(D_5019, k9_relat_1(A_5020, B_5022)) | ~v1_funct_1(A_5020) | ~v1_relat_1(A_5020))), inference(superposition, [status(thm), theory('equality')], [c_94196, c_2])).
% 42.41/30.56  tff(c_136561, plain, (![D_5023, A_5024, B_5025]: (r2_hidden(D_5023, k9_relat_1(A_5024, k1_relat_1(A_5024))) | ~r2_hidden('#skF_4'(A_5024, B_5025, k9_relat_1(A_5024, B_5025), D_5023), k1_relat_1(A_5024)) | ~r2_hidden(D_5023, k9_relat_1(A_5024, B_5025)) | ~v1_funct_1(A_5024) | ~v1_relat_1(A_5024))), inference(resolution, [status(thm)], [c_8, c_136491])).
% 42.41/30.56  tff(c_136581, plain, (![D_5026, A_5027, B_5028]: (r2_hidden(D_5026, k9_relat_1(A_5027, k1_relat_1(A_5027))) | ~r2_hidden(D_5026, k9_relat_1(A_5027, B_5028)) | ~v1_funct_1(A_5027) | ~v1_relat_1(A_5027))), inference(resolution, [status(thm)], [c_8, c_136561])).
% 42.41/30.56  tff(c_136987, plain, (![A_5031, E_5032, B_5033]: (r2_hidden(k1_funct_1(A_5031, E_5032), k9_relat_1(A_5031, k1_relat_1(A_5031))) | ~r2_hidden(E_5032, B_5033) | ~r2_hidden(E_5032, k1_relat_1(A_5031)) | ~v1_funct_1(A_5031) | ~v1_relat_1(A_5031))), inference(resolution, [status(thm)], [c_2, c_136581])).
% 42.41/30.56  tff(c_139497, plain, (![A_5070]: (r2_hidden(k1_funct_1(A_5070, '#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11'))), k9_relat_1(A_5070, k1_relat_1(A_5070))) | ~r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k1_relat_1(A_5070)) | ~v1_funct_1(A_5070) | ~v1_relat_1(A_5070))), inference(resolution, [status(thm)], [c_129998, c_136987])).
% 42.41/30.56  tff(c_139525, plain, (r2_hidden(k1_funct_1('#skF_13', '#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11'))), k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_74, c_139497])).
% 42.41/30.56  tff(c_139540, plain, (r2_hidden(k1_funct_1('#skF_13', '#skF_8'('#skF_13', k9_relat_1('#skF_13', '#skF_11'))), k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_129998, c_74, c_139525])).
% 42.41/30.56  tff(c_153857, plain, (r2_hidden('#skF_7'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k9_relat_1('#skF_13', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_153832, c_139540])).
% 42.41/30.56  tff(c_154078, plain, (![D_90]: (k1_funct_1('#skF_13', D_90)!='#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden(D_90, k1_relat_1('#skF_13')) | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13') | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_153857, c_50])).
% 42.41/30.56  tff(c_154103, plain, (![D_90]: (k1_funct_1('#skF_13', D_90)!='#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden(D_90, '#skF_11') | k9_relat_1('#skF_13', '#skF_11')=k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_154078])).
% 42.41/30.56  tff(c_154358, plain, (![D_5378]: (k1_funct_1('#skF_13', D_5378)!='#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden(D_5378, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_97375, c_154103])).
% 42.41/30.56  tff(c_154379, plain, (![C_91]: (C_91!='#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), C_91), '#skF_11') | ~r2_hidden(C_91, k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_154358])).
% 42.41/30.56  tff(c_154862, plain, (![C_5384]: (C_5384!='#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')) | ~r2_hidden('#skF_10'('#skF_13', k2_relat_1('#skF_13'), C_5384), '#skF_11') | ~r2_hidden(C_5384, k2_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_154379])).
% 42.41/30.56  tff(c_154867, plain, (~r2_hidden('#skF_9'('#skF_13', k9_relat_1('#skF_13', '#skF_11')), k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_94024, c_154862])).
% 42.41/30.56  tff(c_154869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154867, c_130030])).
% 42.41/30.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.41/30.56  
% 42.41/30.56  Inference rules
% 42.41/30.56  ----------------------
% 42.41/30.56  #Ref     : 102
% 42.41/30.56  #Sup     : 33690
% 42.41/30.56  #Fact    : 0
% 42.41/30.56  #Define  : 0
% 42.41/30.56  #Split   : 92
% 42.41/30.56  #Chain   : 0
% 42.41/30.56  #Close   : 0
% 42.41/30.56  
% 42.41/30.56  Ordering : KBO
% 42.41/30.56  
% 42.41/30.56  Simplification rules
% 42.41/30.56  ----------------------
% 42.41/30.56  #Subsume      : 8681
% 42.41/30.56  #Demod        : 32289
% 42.41/30.56  #Tautology    : 3741
% 42.41/30.56  #SimpNegUnit  : 807
% 42.41/30.56  #BackRed      : 690
% 42.41/30.56  
% 42.41/30.56  #Partial instantiations: 0
% 42.41/30.56  #Strategies tried      : 1
% 42.41/30.56  
% 42.41/30.56  Timing (in seconds)
% 42.41/30.56  ----------------------
% 42.41/30.57  Preprocessing        : 0.34
% 42.41/30.57  Parsing              : 0.17
% 42.41/30.57  CNF conversion       : 0.03
% 42.41/30.57  Main loop            : 29.39
% 42.41/30.57  Inferencing          : 7.75
% 42.41/30.57  Reduction            : 8.06
% 42.41/30.57  Demodulation         : 5.89
% 42.41/30.57  BG Simplification    : 0.63
% 42.41/30.57  Subsumption          : 10.59
% 42.41/30.57  Abstraction          : 1.05
% 42.41/30.57  MUC search           : 0.00
% 42.41/30.57  Cooper               : 0.00
% 42.41/30.57  Total                : 29.83
% 42.41/30.57  Index Insertion      : 0.00
% 42.41/30.57  Index Deletion       : 0.00
% 42.41/30.57  Index Matching       : 0.00
% 42.41/30.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
