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
% DateTime   : Thu Dec  3 10:16:32 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 112 expanded)
%              Number of leaves         :   35 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 273 expanded)
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

tff(f_92,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_60])).

tff(c_54,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_67,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76),A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_75] : r1_tarski(A_75,A_75) ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_89,plain,(
    ! [B_80,A_81] :
      ( v4_relat_1(B_80,A_81)
      | ~ r1_tarski(k1_relat_1(B_80),A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_94,plain,(
    ! [B_80] :
      ( v4_relat_1(B_80,k1_relat_1(B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_80,c_89])).

tff(c_103,plain,(
    ! [C_86,A_87,B_88] :
      ( v4_relat_1(C_86,A_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_112,plain,(
    v4_relat_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_103])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [C_83,B_84,A_85] :
      ( r2_hidden(C_83,B_84)
      | ~ r2_hidden(C_83,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [A_95,B_96,B_97] :
      ( r2_hidden('#skF_1'(A_95,B_96),B_97)
      | ~ r1_tarski(A_95,B_97)
      | r1_tarski(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_233,plain,(
    ! [A_118,B_119,B_120,B_121] :
      ( r2_hidden('#skF_1'(A_118,B_119),B_120)
      | ~ r1_tarski(B_121,B_120)
      | ~ r1_tarski(A_118,B_121)
      | r1_tarski(A_118,B_119) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_286,plain,(
    ! [A_143,B_144,A_145,B_146] :
      ( r2_hidden('#skF_1'(A_143,B_144),A_145)
      | ~ r1_tarski(A_143,k1_relat_1(B_146))
      | r1_tarski(A_143,B_144)
      | ~ v4_relat_1(B_146,A_145)
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_12,c_233])).

tff(c_727,plain,(
    ! [B_252,B_253,A_254,B_255] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_252),B_253),A_254)
      | r1_tarski(k1_relat_1(B_252),B_253)
      | ~ v4_relat_1(B_255,A_254)
      | ~ v1_relat_1(B_255)
      | ~ v4_relat_1(B_252,k1_relat_1(B_255))
      | ~ v1_relat_1(B_252) ) ),
    inference(resolution,[status(thm)],[c_12,c_286])).

tff(c_731,plain,(
    ! [B_252,B_253] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_252),B_253),'#skF_6')
      | r1_tarski(k1_relat_1(B_252),B_253)
      | ~ v1_relat_1('#skF_9')
      | ~ v4_relat_1(B_252,k1_relat_1('#skF_9'))
      | ~ v1_relat_1(B_252) ) ),
    inference(resolution,[status(thm)],[c_112,c_727])).

tff(c_739,plain,(
    ! [B_256,B_257] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_256),B_257),'#skF_6')
      | r1_tarski(k1_relat_1(B_256),B_257)
      | ~ v4_relat_1(B_256,k1_relat_1('#skF_9'))
      | ~ v1_relat_1(B_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_731])).

tff(c_752,plain,(
    ! [B_258] :
      ( r1_tarski(k1_relat_1(B_258),'#skF_6')
      | ~ v4_relat_1(B_258,k1_relat_1('#skF_9'))
      | ~ v1_relat_1(B_258) ) ),
    inference(resolution,[status(thm)],[c_739,c_4])).

tff(c_760,plain,
    ( r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_94,c_752])).

tff(c_764,plain,(
    r1_tarski(k1_relat_1('#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_760])).

tff(c_16,plain,(
    ! [A_10,B_33,D_48] :
      ( k1_funct_1(A_10,'#skF_5'(A_10,B_33,k9_relat_1(A_10,B_33),D_48)) = D_48
      | ~ r2_hidden(D_48,k9_relat_1(A_10,B_33))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_380,plain,(
    ! [A_169,B_170,D_171] :
      ( r2_hidden('#skF_5'(A_169,B_170,k9_relat_1(A_169,B_170),D_171),k1_relat_1(A_169))
      | ~ r2_hidden(D_171,k9_relat_1(A_169,B_170))
      | ~ v1_funct_1(A_169)
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1141,plain,(
    ! [A_317,B_318,D_319,B_320] :
      ( r2_hidden('#skF_5'(A_317,B_318,k9_relat_1(A_317,B_318),D_319),B_320)
      | ~ r1_tarski(k1_relat_1(A_317),B_320)
      | ~ r2_hidden(D_319,k9_relat_1(A_317,B_318))
      | ~ v1_funct_1(A_317)
      | ~ v1_relat_1(A_317) ) ),
    inference(resolution,[status(thm)],[c_380,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1221,plain,(
    ! [A_341,B_342,D_343,B_344] :
      ( m1_subset_1('#skF_5'(A_341,B_342,k9_relat_1(A_341,B_342),D_343),B_344)
      | ~ r1_tarski(k1_relat_1(A_341),B_344)
      | ~ r2_hidden(D_343,k9_relat_1(A_341,B_342))
      | ~ v1_funct_1(A_341)
      | ~ v1_relat_1(A_341) ) ),
    inference(resolution,[status(thm)],[c_1141,c_8])).

tff(c_273,plain,(
    ! [A_140,B_141,D_142] :
      ( r2_hidden('#skF_5'(A_140,B_141,k9_relat_1(A_140,B_141),D_142),B_141)
      | ~ r2_hidden(D_142,k9_relat_1(A_140,B_141))
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    ! [F_66] :
      ( k1_funct_1('#skF_9',F_66) != '#skF_10'
      | ~ r2_hidden(F_66,'#skF_8')
      | ~ m1_subset_1(F_66,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_284,plain,(
    ! [A_140,D_142] :
      ( k1_funct_1('#skF_9','#skF_5'(A_140,'#skF_8',k9_relat_1(A_140,'#skF_8'),D_142)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'(A_140,'#skF_8',k9_relat_1(A_140,'#skF_8'),D_142),'#skF_6')
      | ~ r2_hidden(D_142,k9_relat_1(A_140,'#skF_8'))
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(resolution,[status(thm)],[c_273,c_46])).

tff(c_1619,plain,(
    ! [A_401,D_402] :
      ( k1_funct_1('#skF_9','#skF_5'(A_401,'#skF_8',k9_relat_1(A_401,'#skF_8'),D_402)) != '#skF_10'
      | ~ r1_tarski(k1_relat_1(A_401),'#skF_6')
      | ~ r2_hidden(D_402,k9_relat_1(A_401,'#skF_8'))
      | ~ v1_funct_1(A_401)
      | ~ v1_relat_1(A_401) ) ),
    inference(resolution,[status(thm)],[c_1221,c_284])).

tff(c_1623,plain,(
    ! [D_48] :
      ( D_48 != '#skF_10'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
      | ~ r2_hidden(D_48,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_48,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1619])).

tff(c_1632,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_64,c_54,c_764,c_1623])).

tff(c_170,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k7_relset_1(A_104,B_105,C_106,D_107) = k9_relat_1(C_106,D_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_181,plain,(
    ! [D_107] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_107) = k9_relat_1('#skF_9',D_107) ),
    inference(resolution,[status(thm)],[c_50,c_170])).

tff(c_48,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_184,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_48])).

tff(c_1634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1632,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.81  
% 4.51/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.82  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 4.51/1.82  
% 4.51/1.82  %Foreground sorts:
% 4.51/1.82  
% 4.51/1.82  
% 4.51/1.82  %Background operators:
% 4.51/1.82  
% 4.51/1.82  
% 4.51/1.82  %Foreground operators:
% 4.51/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.51/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.82  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.51/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.51/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.82  tff('#skF_10', type, '#skF_10': $i).
% 4.51/1.82  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.51/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.51/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.51/1.82  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.51/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.51/1.82  tff('#skF_9', type, '#skF_9': $i).
% 4.51/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.51/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.82  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.51/1.82  tff('#skF_8', type, '#skF_8': $i).
% 4.51/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.82  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.51/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.51/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.51/1.82  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.51/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.51/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.51/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.51/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.82  
% 4.59/1.83  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 4.59/1.83  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.59/1.83  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.59/1.83  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.59/1.83  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.59/1.83  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 4.59/1.83  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.59/1.83  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.59/1.83  tff(c_50, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.59/1.83  tff(c_60, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.59/1.83  tff(c_64, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_50, c_60])).
% 4.59/1.83  tff(c_54, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.59/1.83  tff(c_67, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75, B_76), A_75) | r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.83  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.83  tff(c_80, plain, (![A_75]: (r1_tarski(A_75, A_75))), inference(resolution, [status(thm)], [c_67, c_4])).
% 4.59/1.83  tff(c_89, plain, (![B_80, A_81]: (v4_relat_1(B_80, A_81) | ~r1_tarski(k1_relat_1(B_80), A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.59/1.83  tff(c_94, plain, (![B_80]: (v4_relat_1(B_80, k1_relat_1(B_80)) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_80, c_89])).
% 4.59/1.83  tff(c_103, plain, (![C_86, A_87, B_88]: (v4_relat_1(C_86, A_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.59/1.83  tff(c_112, plain, (v4_relat_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_103])).
% 4.59/1.83  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.59/1.83  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.83  tff(c_96, plain, (![C_83, B_84, A_85]: (r2_hidden(C_83, B_84) | ~r2_hidden(C_83, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.83  tff(c_135, plain, (![A_95, B_96, B_97]: (r2_hidden('#skF_1'(A_95, B_96), B_97) | ~r1_tarski(A_95, B_97) | r1_tarski(A_95, B_96))), inference(resolution, [status(thm)], [c_6, c_96])).
% 4.59/1.83  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.83  tff(c_233, plain, (![A_118, B_119, B_120, B_121]: (r2_hidden('#skF_1'(A_118, B_119), B_120) | ~r1_tarski(B_121, B_120) | ~r1_tarski(A_118, B_121) | r1_tarski(A_118, B_119))), inference(resolution, [status(thm)], [c_135, c_2])).
% 4.59/1.83  tff(c_286, plain, (![A_143, B_144, A_145, B_146]: (r2_hidden('#skF_1'(A_143, B_144), A_145) | ~r1_tarski(A_143, k1_relat_1(B_146)) | r1_tarski(A_143, B_144) | ~v4_relat_1(B_146, A_145) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_12, c_233])).
% 4.59/1.83  tff(c_727, plain, (![B_252, B_253, A_254, B_255]: (r2_hidden('#skF_1'(k1_relat_1(B_252), B_253), A_254) | r1_tarski(k1_relat_1(B_252), B_253) | ~v4_relat_1(B_255, A_254) | ~v1_relat_1(B_255) | ~v4_relat_1(B_252, k1_relat_1(B_255)) | ~v1_relat_1(B_252))), inference(resolution, [status(thm)], [c_12, c_286])).
% 4.59/1.83  tff(c_731, plain, (![B_252, B_253]: (r2_hidden('#skF_1'(k1_relat_1(B_252), B_253), '#skF_6') | r1_tarski(k1_relat_1(B_252), B_253) | ~v1_relat_1('#skF_9') | ~v4_relat_1(B_252, k1_relat_1('#skF_9')) | ~v1_relat_1(B_252))), inference(resolution, [status(thm)], [c_112, c_727])).
% 4.59/1.83  tff(c_739, plain, (![B_256, B_257]: (r2_hidden('#skF_1'(k1_relat_1(B_256), B_257), '#skF_6') | r1_tarski(k1_relat_1(B_256), B_257) | ~v4_relat_1(B_256, k1_relat_1('#skF_9')) | ~v1_relat_1(B_256))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_731])).
% 4.59/1.83  tff(c_752, plain, (![B_258]: (r1_tarski(k1_relat_1(B_258), '#skF_6') | ~v4_relat_1(B_258, k1_relat_1('#skF_9')) | ~v1_relat_1(B_258))), inference(resolution, [status(thm)], [c_739, c_4])).
% 4.59/1.83  tff(c_760, plain, (r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_94, c_752])).
% 4.59/1.83  tff(c_764, plain, (r1_tarski(k1_relat_1('#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_760])).
% 4.59/1.83  tff(c_16, plain, (![A_10, B_33, D_48]: (k1_funct_1(A_10, '#skF_5'(A_10, B_33, k9_relat_1(A_10, B_33), D_48))=D_48 | ~r2_hidden(D_48, k9_relat_1(A_10, B_33)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.59/1.83  tff(c_380, plain, (![A_169, B_170, D_171]: (r2_hidden('#skF_5'(A_169, B_170, k9_relat_1(A_169, B_170), D_171), k1_relat_1(A_169)) | ~r2_hidden(D_171, k9_relat_1(A_169, B_170)) | ~v1_funct_1(A_169) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.59/1.83  tff(c_1141, plain, (![A_317, B_318, D_319, B_320]: (r2_hidden('#skF_5'(A_317, B_318, k9_relat_1(A_317, B_318), D_319), B_320) | ~r1_tarski(k1_relat_1(A_317), B_320) | ~r2_hidden(D_319, k9_relat_1(A_317, B_318)) | ~v1_funct_1(A_317) | ~v1_relat_1(A_317))), inference(resolution, [status(thm)], [c_380, c_2])).
% 4.59/1.83  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.59/1.83  tff(c_1221, plain, (![A_341, B_342, D_343, B_344]: (m1_subset_1('#skF_5'(A_341, B_342, k9_relat_1(A_341, B_342), D_343), B_344) | ~r1_tarski(k1_relat_1(A_341), B_344) | ~r2_hidden(D_343, k9_relat_1(A_341, B_342)) | ~v1_funct_1(A_341) | ~v1_relat_1(A_341))), inference(resolution, [status(thm)], [c_1141, c_8])).
% 4.59/1.83  tff(c_273, plain, (![A_140, B_141, D_142]: (r2_hidden('#skF_5'(A_140, B_141, k9_relat_1(A_140, B_141), D_142), B_141) | ~r2_hidden(D_142, k9_relat_1(A_140, B_141)) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.59/1.83  tff(c_46, plain, (![F_66]: (k1_funct_1('#skF_9', F_66)!='#skF_10' | ~r2_hidden(F_66, '#skF_8') | ~m1_subset_1(F_66, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.59/1.83  tff(c_284, plain, (![A_140, D_142]: (k1_funct_1('#skF_9', '#skF_5'(A_140, '#skF_8', k9_relat_1(A_140, '#skF_8'), D_142))!='#skF_10' | ~m1_subset_1('#skF_5'(A_140, '#skF_8', k9_relat_1(A_140, '#skF_8'), D_142), '#skF_6') | ~r2_hidden(D_142, k9_relat_1(A_140, '#skF_8')) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(resolution, [status(thm)], [c_273, c_46])).
% 4.59/1.83  tff(c_1619, plain, (![A_401, D_402]: (k1_funct_1('#skF_9', '#skF_5'(A_401, '#skF_8', k9_relat_1(A_401, '#skF_8'), D_402))!='#skF_10' | ~r1_tarski(k1_relat_1(A_401), '#skF_6') | ~r2_hidden(D_402, k9_relat_1(A_401, '#skF_8')) | ~v1_funct_1(A_401) | ~v1_relat_1(A_401))), inference(resolution, [status(thm)], [c_1221, c_284])).
% 4.59/1.83  tff(c_1623, plain, (![D_48]: (D_48!='#skF_10' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~r2_hidden(D_48, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_48, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1619])).
% 4.59/1.83  tff(c_1632, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_64, c_54, c_764, c_1623])).
% 4.59/1.83  tff(c_170, plain, (![A_104, B_105, C_106, D_107]: (k7_relset_1(A_104, B_105, C_106, D_107)=k9_relat_1(C_106, D_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.59/1.83  tff(c_181, plain, (![D_107]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_107)=k9_relat_1('#skF_9', D_107))), inference(resolution, [status(thm)], [c_50, c_170])).
% 4.59/1.83  tff(c_48, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.59/1.83  tff(c_184, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_48])).
% 4.59/1.83  tff(c_1634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1632, c_184])).
% 4.59/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.83  
% 4.59/1.83  Inference rules
% 4.59/1.83  ----------------------
% 4.59/1.83  #Ref     : 0
% 4.59/1.83  #Sup     : 336
% 4.59/1.83  #Fact    : 0
% 4.59/1.83  #Define  : 0
% 4.59/1.83  #Split   : 6
% 4.59/1.83  #Chain   : 0
% 4.59/1.83  #Close   : 0
% 4.59/1.83  
% 4.59/1.83  Ordering : KBO
% 4.59/1.83  
% 4.59/1.83  Simplification rules
% 4.59/1.83  ----------------------
% 4.59/1.83  #Subsume      : 72
% 4.59/1.83  #Demod        : 41
% 4.59/1.83  #Tautology    : 19
% 4.59/1.83  #SimpNegUnit  : 1
% 4.59/1.83  #BackRed      : 4
% 4.59/1.83  
% 4.59/1.83  #Partial instantiations: 0
% 4.59/1.83  #Strategies tried      : 1
% 4.59/1.83  
% 4.59/1.83  Timing (in seconds)
% 4.59/1.83  ----------------------
% 4.59/1.83  Preprocessing        : 0.34
% 4.59/1.83  Parsing              : 0.18
% 4.59/1.83  CNF conversion       : 0.03
% 4.59/1.83  Main loop            : 0.69
% 4.59/1.83  Inferencing          : 0.28
% 4.59/1.83  Reduction            : 0.17
% 4.59/1.83  Demodulation         : 0.12
% 4.59/1.83  BG Simplification    : 0.03
% 4.59/1.83  Subsumption          : 0.15
% 4.59/1.83  Abstraction          : 0.04
% 4.59/1.83  MUC search           : 0.00
% 4.59/1.83  Cooper               : 0.00
% 4.59/1.83  Total                : 1.06
% 4.59/1.83  Index Insertion      : 0.00
% 4.59/1.83  Index Deletion       : 0.00
% 4.59/1.83  Index Matching       : 0.00
% 4.59/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
