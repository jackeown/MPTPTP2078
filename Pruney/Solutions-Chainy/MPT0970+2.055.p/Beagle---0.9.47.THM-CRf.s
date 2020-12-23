%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:27 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 211 expanded)
%              Number of leaves         :   38 (  89 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 516 expanded)
%              Number of equality atoms :   30 ( 124 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_170,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_174,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_170])).

tff(c_58,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_175,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_58])).

tff(c_202,plain,(
    ! [A_115,B_116,C_117] :
      ( m1_subset_1(k2_relset_1(A_115,B_116,C_117),k1_zfmisc_1(B_116))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_219,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_202])).

tff(c_225,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_219])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [C_93,A_94,B_95] :
      ( r2_hidden(C_93,A_94)
      | ~ r2_hidden(C_93,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_181,plain,(
    ! [A_110,B_111,A_112] :
      ( r2_hidden('#skF_1'(A_110,B_111),A_112)
      | ~ m1_subset_1(A_110,k1_zfmisc_1(A_112))
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_192,plain,(
    ! [A_110,A_112] :
      ( ~ m1_subset_1(A_110,k1_zfmisc_1(A_112))
      | r1_tarski(A_110,A_112) ) ),
    inference(resolution,[status(thm)],[c_181,c_4])).

tff(c_232,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_225,c_192])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_235,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_232,c_8])).

tff(c_238,plain,(
    ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_235])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_161,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_165,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_161])).

tff(c_1145,plain,(
    ! [B_259,A_260,C_261] :
      ( k1_xboole_0 = B_259
      | k1_relset_1(A_260,B_259,C_261) = A_260
      | ~ v1_funct_2(C_261,A_260,B_259)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_260,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1152,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_1145])).

tff(c_1156,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_165,c_1152])).

tff(c_1157,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1156])).

tff(c_68,plain,(
    ! [D_73] :
      ( r2_hidden('#skF_9'(D_73),'#skF_6')
      | ~ r2_hidden(D_73,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_121,plain,(
    ! [C_90,B_91,A_92] :
      ( r2_hidden(C_90,B_91)
      | ~ r2_hidden(C_90,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_127,plain,(
    ! [D_73,B_91] :
      ( r2_hidden('#skF_9'(D_73),B_91)
      | ~ r1_tarski('#skF_6',B_91)
      | ~ r2_hidden(D_73,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_121])).

tff(c_20,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_107,plain,(
    ! [B_86,A_87] :
      ( v1_relat_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87))
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_110,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_60,c_107])).

tff(c_113,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_110])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_66,plain,(
    ! [D_73] :
      ( k1_funct_1('#skF_8','#skF_9'(D_73)) = D_73
      | ~ r2_hidden(D_73,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_239,plain,(
    ! [A_118,D_119] :
      ( r2_hidden(k1_funct_1(A_118,D_119),k2_relat_1(A_118))
      | ~ r2_hidden(D_119,k1_relat_1(A_118))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_246,plain,(
    ! [D_73] :
      ( r2_hidden(D_73,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_73),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_73,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_239])).

tff(c_252,plain,(
    ! [D_120] :
      ( r2_hidden(D_120,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_120),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_120,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_64,c_246])).

tff(c_262,plain,(
    ! [D_73] :
      ( r2_hidden(D_73,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_73,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_127,c_252])).

tff(c_263,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_1159,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_263])).

tff(c_1164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1159])).

tff(c_1165,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1156])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1179,plain,(
    ! [A_8] : r1_tarski('#skF_7',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1165,c_14])).

tff(c_1245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_238])).

tff(c_1251,plain,(
    ! [D_263] :
      ( r2_hidden(D_263,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_263,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_1278,plain,(
    ! [A_268] :
      ( r1_tarski(A_268,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_268,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1251,c_4])).

tff(c_1290,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_1278])).

tff(c_1296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_238,c_1290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:30:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.64  
% 3.90/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.64  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 3.90/1.64  
% 3.90/1.64  %Foreground sorts:
% 3.90/1.64  
% 3.90/1.64  
% 3.90/1.64  %Background operators:
% 3.90/1.64  
% 3.90/1.64  
% 3.90/1.64  %Foreground operators:
% 3.90/1.64  tff('#skF_9', type, '#skF_9': $i > $i).
% 3.90/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.90/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.90/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.90/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.90/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.90/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.90/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.90/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.90/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.90/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.90/1.64  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.90/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.90/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.90/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.90/1.64  tff('#skF_8', type, '#skF_8': $i).
% 3.90/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.90/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.90/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.90/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.90/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.90/1.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.90/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.90/1.64  
% 3.90/1.66  tff(f_120, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 3.90/1.66  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.90/1.66  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.90/1.66  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.90/1.66  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.90/1.66  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.90/1.66  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.90/1.66  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.90/1.66  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.90/1.66  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.90/1.66  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.90/1.66  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.90/1.66  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.90/1.66  tff(c_170, plain, (![A_106, B_107, C_108]: (k2_relset_1(A_106, B_107, C_108)=k2_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.90/1.66  tff(c_174, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_170])).
% 3.90/1.66  tff(c_58, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.90/1.66  tff(c_175, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_58])).
% 3.90/1.66  tff(c_202, plain, (![A_115, B_116, C_117]: (m1_subset_1(k2_relset_1(A_115, B_116, C_117), k1_zfmisc_1(B_116)) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.90/1.66  tff(c_219, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_174, c_202])).
% 3.90/1.66  tff(c_225, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_219])).
% 3.90/1.66  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.90/1.66  tff(c_128, plain, (![C_93, A_94, B_95]: (r2_hidden(C_93, A_94) | ~r2_hidden(C_93, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.90/1.66  tff(c_181, plain, (![A_110, B_111, A_112]: (r2_hidden('#skF_1'(A_110, B_111), A_112) | ~m1_subset_1(A_110, k1_zfmisc_1(A_112)) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_6, c_128])).
% 3.90/1.66  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.90/1.66  tff(c_192, plain, (![A_110, A_112]: (~m1_subset_1(A_110, k1_zfmisc_1(A_112)) | r1_tarski(A_110, A_112))), inference(resolution, [status(thm)], [c_181, c_4])).
% 3.90/1.66  tff(c_232, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_225, c_192])).
% 3.90/1.66  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.90/1.66  tff(c_235, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_232, c_8])).
% 3.90/1.66  tff(c_238, plain, (~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_175, c_235])).
% 3.90/1.66  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.90/1.66  tff(c_62, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.90/1.66  tff(c_161, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.90/1.66  tff(c_165, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_161])).
% 3.90/1.66  tff(c_1145, plain, (![B_259, A_260, C_261]: (k1_xboole_0=B_259 | k1_relset_1(A_260, B_259, C_261)=A_260 | ~v1_funct_2(C_261, A_260, B_259) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_260, B_259))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.90/1.66  tff(c_1152, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_1145])).
% 3.90/1.66  tff(c_1156, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_165, c_1152])).
% 3.90/1.66  tff(c_1157, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_1156])).
% 3.90/1.66  tff(c_68, plain, (![D_73]: (r2_hidden('#skF_9'(D_73), '#skF_6') | ~r2_hidden(D_73, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.90/1.66  tff(c_121, plain, (![C_90, B_91, A_92]: (r2_hidden(C_90, B_91) | ~r2_hidden(C_90, A_92) | ~r1_tarski(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.90/1.66  tff(c_127, plain, (![D_73, B_91]: (r2_hidden('#skF_9'(D_73), B_91) | ~r1_tarski('#skF_6', B_91) | ~r2_hidden(D_73, '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_121])).
% 3.90/1.66  tff(c_20, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.90/1.66  tff(c_107, plain, (![B_86, A_87]: (v1_relat_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.90/1.66  tff(c_110, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_107])).
% 3.90/1.66  tff(c_113, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_110])).
% 3.90/1.66  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.90/1.66  tff(c_66, plain, (![D_73]: (k1_funct_1('#skF_8', '#skF_9'(D_73))=D_73 | ~r2_hidden(D_73, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.90/1.66  tff(c_239, plain, (![A_118, D_119]: (r2_hidden(k1_funct_1(A_118, D_119), k2_relat_1(A_118)) | ~r2_hidden(D_119, k1_relat_1(A_118)) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.90/1.66  tff(c_246, plain, (![D_73]: (r2_hidden(D_73, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_73), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_73, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_239])).
% 3.90/1.66  tff(c_252, plain, (![D_120]: (r2_hidden(D_120, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_120), k1_relat_1('#skF_8')) | ~r2_hidden(D_120, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_64, c_246])).
% 3.90/1.66  tff(c_262, plain, (![D_73]: (r2_hidden(D_73, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_73, '#skF_7'))), inference(resolution, [status(thm)], [c_127, c_252])).
% 3.90/1.66  tff(c_263, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_262])).
% 3.90/1.66  tff(c_1159, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1157, c_263])).
% 3.90/1.66  tff(c_1164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1159])).
% 3.90/1.66  tff(c_1165, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1156])).
% 3.90/1.66  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.90/1.66  tff(c_1179, plain, (![A_8]: (r1_tarski('#skF_7', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_1165, c_14])).
% 3.90/1.66  tff(c_1245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1179, c_238])).
% 3.90/1.66  tff(c_1251, plain, (![D_263]: (r2_hidden(D_263, k2_relat_1('#skF_8')) | ~r2_hidden(D_263, '#skF_7'))), inference(splitRight, [status(thm)], [c_262])).
% 3.90/1.66  tff(c_1278, plain, (![A_268]: (r1_tarski(A_268, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_268, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_1251, c_4])).
% 3.90/1.66  tff(c_1290, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_1278])).
% 3.90/1.66  tff(c_1296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_238, c_1290])).
% 3.90/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.66  
% 3.90/1.66  Inference rules
% 3.90/1.66  ----------------------
% 3.90/1.66  #Ref     : 0
% 3.90/1.66  #Sup     : 268
% 3.90/1.66  #Fact    : 0
% 3.90/1.66  #Define  : 0
% 3.90/1.66  #Split   : 23
% 3.90/1.66  #Chain   : 0
% 3.90/1.66  #Close   : 0
% 3.90/1.66  
% 3.90/1.66  Ordering : KBO
% 3.90/1.66  
% 3.90/1.66  Simplification rules
% 3.90/1.66  ----------------------
% 3.90/1.66  #Subsume      : 67
% 3.90/1.66  #Demod        : 108
% 3.90/1.66  #Tautology    : 53
% 3.90/1.66  #SimpNegUnit  : 2
% 3.90/1.66  #BackRed      : 42
% 3.90/1.66  
% 3.90/1.66  #Partial instantiations: 0
% 3.90/1.66  #Strategies tried      : 1
% 3.90/1.66  
% 3.90/1.66  Timing (in seconds)
% 3.90/1.66  ----------------------
% 3.90/1.66  Preprocessing        : 0.35
% 3.90/1.66  Parsing              : 0.18
% 3.90/1.66  CNF conversion       : 0.03
% 3.90/1.66  Main loop            : 0.56
% 3.90/1.66  Inferencing          : 0.18
% 3.90/1.66  Reduction            : 0.16
% 3.90/1.66  Demodulation         : 0.10
% 3.90/1.66  BG Simplification    : 0.03
% 3.90/1.66  Subsumption          : 0.15
% 3.90/1.66  Abstraction          : 0.03
% 3.90/1.66  MUC search           : 0.00
% 3.90/1.66  Cooper               : 0.00
% 3.90/1.66  Total                : 0.94
% 3.90/1.66  Index Insertion      : 0.00
% 3.90/1.66  Index Deletion       : 0.00
% 3.90/1.66  Index Matching       : 0.00
% 3.90/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
