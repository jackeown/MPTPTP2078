%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:28 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 153 expanded)
%              Number of leaves         :   40 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 290 expanded)
%              Number of equality atoms :   26 (  59 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_52,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30,plain,(
    ! [A_33,B_34] : v1_relat_1(k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_83,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_86,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_54,c_83])).

tff(c_89,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_86])).

tff(c_38,plain,(
    ! [A_35] :
      ( k2_relat_1(A_35) = k1_xboole_0
      | k1_relat_1(A_35) != k1_xboole_0
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_115,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_89,c_38])).

tff(c_118,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_179,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_188,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_179])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_175,plain,(
    ! [C_92,B_93,A_94] :
      ( r2_hidden(C_92,B_93)
      | ~ r2_hidden(C_92,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_241,plain,(
    ! [A_110,B_111,B_112] :
      ( r2_hidden('#skF_1'(A_110,B_111),B_112)
      | ~ r1_tarski(A_110,B_112)
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_273,plain,(
    ! [A_117,B_118,B_119] :
      ( m1_subset_1('#skF_1'(A_117,B_118),B_119)
      | ~ r1_tarski(A_117,B_119)
      | r1_tarski(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_241,c_10])).

tff(c_218,plain,(
    ! [A_105,B_106,C_107] :
      ( k1_relset_1(A_105,B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_227,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_218])).

tff(c_90,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74),A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [D_58] :
      ( ~ r2_hidden(D_58,k1_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ m1_subset_1(D_58,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_107,plain,(
    ! [B_74] :
      ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_7','#skF_6','#skF_8'),B_74),'#skF_7')
      | r1_tarski(k1_relset_1('#skF_7','#skF_6','#skF_8'),B_74) ) ),
    inference(resolution,[status(thm)],[c_90,c_50])).

tff(c_228,plain,(
    ! [B_74] :
      ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_8'),B_74),'#skF_7')
      | r1_tarski(k1_relat_1('#skF_8'),B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_227,c_107])).

tff(c_298,plain,(
    ! [B_118] :
      ( ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_7')
      | r1_tarski(k1_relat_1('#skF_8'),B_118) ) ),
    inference(resolution,[status(thm)],[c_273,c_228])).

tff(c_304,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_316,plain,
    ( ~ v4_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_304])).

tff(c_320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_188,c_316])).

tff(c_321,plain,(
    ! [B_118] : r1_tarski(k1_relat_1('#skF_8'),B_118) ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_647,plain,(
    ! [A_155,B_156] :
      ( r2_hidden(k4_tarski('#skF_2'(A_155,B_156),'#skF_3'(A_155,B_156)),A_155)
      | r2_hidden('#skF_4'(A_155,B_156),B_156)
      | k1_relat_1(A_155) = B_156 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_361,plain,(
    ! [C_127,A_128] :
      ( r2_hidden(k4_tarski(C_127,'#skF_5'(A_128,k1_relat_1(A_128),C_127)),A_128)
      | ~ r2_hidden(C_127,k1_relat_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_379,plain,(
    ! [C_127] :
      ( r2_hidden(k4_tarski(C_127,'#skF_5'(k1_xboole_0,k1_xboole_0,C_127)),k1_xboole_0)
      | ~ r2_hidden(C_127,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_361])).

tff(c_473,plain,(
    ! [C_139] :
      ( r2_hidden(k4_tarski(C_139,'#skF_5'(k1_xboole_0,k1_xboole_0,C_139)),k1_xboole_0)
      | ~ r2_hidden(C_139,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_379])).

tff(c_40,plain,(
    ! [B_37,A_36] :
      ( ~ r1_tarski(B_37,A_36)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_481,plain,(
    ! [C_139] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_139,'#skF_5'(k1_xboole_0,k1_xboole_0,C_139)))
      | ~ r2_hidden(C_139,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_473,c_40])).

tff(c_492,plain,(
    ! [C_139] : ~ r2_hidden(C_139,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_481])).

tff(c_659,plain,(
    ! [B_156] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_156),B_156)
      | k1_relat_1(k1_xboole_0) = B_156 ) ),
    inference(resolution,[status(thm)],[c_647,c_492])).

tff(c_720,plain,(
    ! [B_158] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_158),B_158)
      | k1_xboole_0 = B_158 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_659])).

tff(c_800,plain,(
    ! [B_160] :
      ( ~ r1_tarski(B_160,'#skF_4'(k1_xboole_0,B_160))
      | k1_xboole_0 = B_160 ) ),
    inference(resolution,[status(thm)],[c_720,c_40])).

tff(c_808,plain,(
    k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_321,c_800])).

tff(c_821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_808])).

tff(c_822,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_1083,plain,(
    ! [A_209,B_210,C_211] :
      ( k2_relset_1(A_209,B_210,C_211) = k2_relat_1(C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1094,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_1083])).

tff(c_1098,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_822,c_1094])).

tff(c_1100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1098])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.66  
% 3.08/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.66  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 3.08/1.66  
% 3.08/1.66  %Foreground sorts:
% 3.08/1.66  
% 3.08/1.66  
% 3.08/1.66  %Background operators:
% 3.08/1.66  
% 3.08/1.66  
% 3.08/1.66  %Foreground operators:
% 3.08/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.08/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.08/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.66  tff('#skF_7', type, '#skF_7': $i).
% 3.08/1.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.08/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.08/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.08/1.66  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.08/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.08/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.08/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.66  tff('#skF_8', type, '#skF_8': $i).
% 3.08/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.08/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.08/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.08/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.66  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.08/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.66  
% 3.47/1.68  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 3.47/1.68  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.47/1.68  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.47/1.68  tff(f_70, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.47/1.68  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.47/1.68  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.47/1.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.47/1.68  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.47/1.68  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.47/1.68  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.47/1.68  tff(f_59, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.47/1.68  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.47/1.68  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.47/1.68  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.47/1.68  tff(c_52, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.47/1.68  tff(c_30, plain, (![A_33, B_34]: (v1_relat_1(k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.47/1.68  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.47/1.68  tff(c_83, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.47/1.68  tff(c_86, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_54, c_83])).
% 3.47/1.68  tff(c_89, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_86])).
% 3.47/1.68  tff(c_38, plain, (![A_35]: (k2_relat_1(A_35)=k1_xboole_0 | k1_relat_1(A_35)!=k1_xboole_0 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.47/1.68  tff(c_115, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_8')!=k1_xboole_0), inference(resolution, [status(thm)], [c_89, c_38])).
% 3.47/1.68  tff(c_118, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_115])).
% 3.47/1.68  tff(c_179, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.47/1.68  tff(c_188, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_179])).
% 3.47/1.68  tff(c_16, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.47/1.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.68  tff(c_175, plain, (![C_92, B_93, A_94]: (r2_hidden(C_92, B_93) | ~r2_hidden(C_92, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.68  tff(c_241, plain, (![A_110, B_111, B_112]: (r2_hidden('#skF_1'(A_110, B_111), B_112) | ~r1_tarski(A_110, B_112) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_6, c_175])).
% 3.47/1.68  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.68  tff(c_273, plain, (![A_117, B_118, B_119]: (m1_subset_1('#skF_1'(A_117, B_118), B_119) | ~r1_tarski(A_117, B_119) | r1_tarski(A_117, B_118))), inference(resolution, [status(thm)], [c_241, c_10])).
% 3.47/1.68  tff(c_218, plain, (![A_105, B_106, C_107]: (k1_relset_1(A_105, B_106, C_107)=k1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.47/1.68  tff(c_227, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_218])).
% 3.47/1.68  tff(c_90, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74), A_73) | r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.68  tff(c_50, plain, (![D_58]: (~r2_hidden(D_58, k1_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~m1_subset_1(D_58, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.47/1.68  tff(c_107, plain, (![B_74]: (~m1_subset_1('#skF_1'(k1_relset_1('#skF_7', '#skF_6', '#skF_8'), B_74), '#skF_7') | r1_tarski(k1_relset_1('#skF_7', '#skF_6', '#skF_8'), B_74))), inference(resolution, [status(thm)], [c_90, c_50])).
% 3.47/1.68  tff(c_228, plain, (![B_74]: (~m1_subset_1('#skF_1'(k1_relat_1('#skF_8'), B_74), '#skF_7') | r1_tarski(k1_relat_1('#skF_8'), B_74))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_227, c_107])).
% 3.47/1.68  tff(c_298, plain, (![B_118]: (~r1_tarski(k1_relat_1('#skF_8'), '#skF_7') | r1_tarski(k1_relat_1('#skF_8'), B_118))), inference(resolution, [status(thm)], [c_273, c_228])).
% 3.47/1.68  tff(c_304, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_298])).
% 3.47/1.68  tff(c_316, plain, (~v4_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_16, c_304])).
% 3.47/1.68  tff(c_320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_188, c_316])).
% 3.47/1.68  tff(c_321, plain, (![B_118]: (r1_tarski(k1_relat_1('#skF_8'), B_118))), inference(splitRight, [status(thm)], [c_298])).
% 3.47/1.68  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.47/1.68  tff(c_647, plain, (![A_155, B_156]: (r2_hidden(k4_tarski('#skF_2'(A_155, B_156), '#skF_3'(A_155, B_156)), A_155) | r2_hidden('#skF_4'(A_155, B_156), B_156) | k1_relat_1(A_155)=B_156)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.47/1.68  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.47/1.68  tff(c_361, plain, (![C_127, A_128]: (r2_hidden(k4_tarski(C_127, '#skF_5'(A_128, k1_relat_1(A_128), C_127)), A_128) | ~r2_hidden(C_127, k1_relat_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.47/1.68  tff(c_379, plain, (![C_127]: (r2_hidden(k4_tarski(C_127, '#skF_5'(k1_xboole_0, k1_xboole_0, C_127)), k1_xboole_0) | ~r2_hidden(C_127, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_361])).
% 3.47/1.68  tff(c_473, plain, (![C_139]: (r2_hidden(k4_tarski(C_139, '#skF_5'(k1_xboole_0, k1_xboole_0, C_139)), k1_xboole_0) | ~r2_hidden(C_139, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_379])).
% 3.47/1.68  tff(c_40, plain, (![B_37, A_36]: (~r1_tarski(B_37, A_36) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.47/1.68  tff(c_481, plain, (![C_139]: (~r1_tarski(k1_xboole_0, k4_tarski(C_139, '#skF_5'(k1_xboole_0, k1_xboole_0, C_139))) | ~r2_hidden(C_139, k1_xboole_0))), inference(resolution, [status(thm)], [c_473, c_40])).
% 3.47/1.68  tff(c_492, plain, (![C_139]: (~r2_hidden(C_139, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_481])).
% 3.47/1.68  tff(c_659, plain, (![B_156]: (r2_hidden('#skF_4'(k1_xboole_0, B_156), B_156) | k1_relat_1(k1_xboole_0)=B_156)), inference(resolution, [status(thm)], [c_647, c_492])).
% 3.47/1.68  tff(c_720, plain, (![B_158]: (r2_hidden('#skF_4'(k1_xboole_0, B_158), B_158) | k1_xboole_0=B_158)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_659])).
% 3.47/1.68  tff(c_800, plain, (![B_160]: (~r1_tarski(B_160, '#skF_4'(k1_xboole_0, B_160)) | k1_xboole_0=B_160)), inference(resolution, [status(thm)], [c_720, c_40])).
% 3.47/1.68  tff(c_808, plain, (k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_321, c_800])).
% 3.47/1.68  tff(c_821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_808])).
% 3.47/1.68  tff(c_822, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_115])).
% 3.47/1.68  tff(c_1083, plain, (![A_209, B_210, C_211]: (k2_relset_1(A_209, B_210, C_211)=k2_relat_1(C_211) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.47/1.68  tff(c_1094, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_1083])).
% 3.47/1.68  tff(c_1098, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_822, c_1094])).
% 3.47/1.68  tff(c_1100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1098])).
% 3.47/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.68  
% 3.47/1.68  Inference rules
% 3.47/1.68  ----------------------
% 3.47/1.68  #Ref     : 0
% 3.47/1.68  #Sup     : 208
% 3.47/1.68  #Fact    : 0
% 3.47/1.68  #Define  : 0
% 3.47/1.68  #Split   : 4
% 3.47/1.68  #Chain   : 0
% 3.47/1.68  #Close   : 0
% 3.47/1.68  
% 3.47/1.68  Ordering : KBO
% 3.47/1.68  
% 3.47/1.68  Simplification rules
% 3.47/1.68  ----------------------
% 3.47/1.68  #Subsume      : 36
% 3.47/1.68  #Demod        : 100
% 3.47/1.68  #Tautology    : 72
% 3.47/1.68  #SimpNegUnit  : 5
% 3.47/1.68  #BackRed      : 9
% 3.47/1.68  
% 3.47/1.68  #Partial instantiations: 0
% 3.47/1.68  #Strategies tried      : 1
% 3.47/1.68  
% 3.47/1.68  Timing (in seconds)
% 3.47/1.68  ----------------------
% 3.47/1.68  Preprocessing        : 0.39
% 3.47/1.68  Parsing              : 0.21
% 3.47/1.68  CNF conversion       : 0.03
% 3.47/1.68  Main loop            : 0.37
% 3.47/1.68  Inferencing          : 0.14
% 3.47/1.68  Reduction            : 0.11
% 3.47/1.68  Demodulation         : 0.08
% 3.47/1.68  BG Simplification    : 0.02
% 3.47/1.68  Subsumption          : 0.07
% 3.47/1.68  Abstraction          : 0.02
% 3.47/1.68  MUC search           : 0.00
% 3.47/1.68  Cooper               : 0.00
% 3.47/1.68  Total                : 0.80
% 3.47/1.68  Index Insertion      : 0.00
% 3.47/1.68  Index Deletion       : 0.00
% 3.47/1.68  Index Matching       : 0.00
% 3.47/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
