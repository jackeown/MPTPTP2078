%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:01 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 175 expanded)
%              Number of leaves         :   48 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 337 expanded)
%              Number of equality atoms :   30 (  68 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_117,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_30,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_102,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_105,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_102])).

tff(c_108,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_105])).

tff(c_40,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k9_relat_1(B_32,A_31),k2_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_182,plain,(
    ! [B_105,A_106] :
      ( k1_tarski(k1_funct_1(B_105,A_106)) = k2_relat_1(B_105)
      | k1_tarski(A_106) != k1_relat_1(B_105)
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_54,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7','#skF_6'),k1_tarski(k1_funct_1('#skF_7','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_191,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7','#skF_6'),k2_relat_1('#skF_7'))
    | k1_tarski('#skF_4') != k1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_54])).

tff(c_203,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7','#skF_6'),k2_relat_1('#skF_7'))
    | k1_tarski('#skF_4') != k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_62,c_191])).

tff(c_334,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_110,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_114,plain,(
    v4_relat_1('#skF_7',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_110])).

tff(c_141,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(k1_relat_1(B_91),A_92)
      | ~ v4_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( k1_tarski(B_17) = A_16
      | k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_tarski(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_626,plain,(
    ! [B_145,B_146] :
      ( k1_tarski(B_145) = k1_relat_1(B_146)
      | k1_relat_1(B_146) = k1_xboole_0
      | ~ v4_relat_1(B_146,k1_tarski(B_145))
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_141,c_18])).

tff(c_632,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_7')
    | k1_relat_1('#skF_7') = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_114,c_626])).

tff(c_635,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_7')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_632])).

tff(c_636,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_635])).

tff(c_52,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_3'(A_42),A_42)
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_267,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden('#skF_2'(A_113,B_114,C_115),k1_relat_1(C_115))
      | ~ r2_hidden(A_113,k9_relat_1(C_115,B_114))
      | ~ v1_relat_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_335,plain,(
    ! [C_121,A_122,B_123] :
      ( ~ v1_xboole_0(k1_relat_1(C_121))
      | ~ r2_hidden(A_122,k9_relat_1(C_121,B_123))
      | ~ v1_relat_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_267,c_2])).

tff(c_359,plain,(
    ! [C_121,B_123] :
      ( ~ v1_xboole_0(k1_relat_1(C_121))
      | ~ v1_relat_1(C_121)
      | k9_relat_1(C_121,B_123) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_335])).

tff(c_640,plain,(
    ! [B_123] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1('#skF_7')
      | k9_relat_1('#skF_7',B_123) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_359])).

tff(c_653,plain,(
    ! [B_123] : k9_relat_1('#skF_7',B_123) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_6,c_640])).

tff(c_417,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k7_relset_1(A_130,B_131,C_132,D_133) = k9_relat_1(C_132,D_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_420,plain,(
    ! [D_133] : k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7',D_133) = k9_relat_1('#skF_7',D_133) ),
    inference(resolution,[status(thm)],[c_58,c_417])).

tff(c_421,plain,(
    ~ r1_tarski(k9_relat_1('#skF_7','#skF_6'),k1_tarski(k1_funct_1('#skF_7','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_54])).

tff(c_701,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_7','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_421])).

tff(c_706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_701])).

tff(c_708,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_711,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_58])).

tff(c_753,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( k7_relset_1(A_151,B_152,C_153,D_154) = k9_relat_1(C_153,D_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_756,plain,(
    ! [D_154] : k7_relset_1(k1_relat_1('#skF_7'),'#skF_5','#skF_7',D_154) = k9_relat_1('#skF_7',D_154) ),
    inference(resolution,[status(thm)],[c_711,c_753])).

tff(c_707,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7','#skF_6'),k2_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_752,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_7'),'#skF_5','#skF_7','#skF_6'),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_707])).

tff(c_774,plain,(
    ~ r1_tarski(k9_relat_1('#skF_7','#skF_6'),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_752])).

tff(c_786,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_774])).

tff(c_790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_786])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:02:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.42  
% 2.97/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.97/1.42  
% 2.97/1.42  %Foreground sorts:
% 2.97/1.42  
% 2.97/1.42  
% 2.97/1.42  %Background operators:
% 2.97/1.42  
% 2.97/1.42  
% 2.97/1.42  %Foreground operators:
% 2.97/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.97/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.97/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.97/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.97/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.97/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.97/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.97/1.42  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.97/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.97/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.97/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.97/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.97/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.97/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.97/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.97/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.97/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.97/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.42  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.97/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.97/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.42  
% 2.97/1.44  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.97/1.44  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.97/1.44  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.97/1.44  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.97/1.44  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.97/1.44  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.97/1.44  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.97/1.44  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.97/1.44  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.97/1.44  tff(f_48, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.97/1.44  tff(f_117, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.97/1.44  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.97/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.97/1.44  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.97/1.44  tff(c_30, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.97/1.44  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.97/1.44  tff(c_102, plain, (![B_76, A_77]: (v1_relat_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.97/1.44  tff(c_105, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_102])).
% 2.97/1.44  tff(c_108, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_105])).
% 2.97/1.44  tff(c_40, plain, (![B_32, A_31]: (r1_tarski(k9_relat_1(B_32, A_31), k2_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.97/1.44  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.97/1.44  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.44  tff(c_62, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.97/1.44  tff(c_182, plain, (![B_105, A_106]: (k1_tarski(k1_funct_1(B_105, A_106))=k2_relat_1(B_105) | k1_tarski(A_106)!=k1_relat_1(B_105) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.97/1.44  tff(c_54, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', '#skF_6'), k1_tarski(k1_funct_1('#skF_7', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.97/1.44  tff(c_191, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', '#skF_6'), k2_relat_1('#skF_7')) | k1_tarski('#skF_4')!=k1_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_182, c_54])).
% 2.97/1.44  tff(c_203, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', '#skF_6'), k2_relat_1('#skF_7')) | k1_tarski('#skF_4')!=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_62, c_191])).
% 2.97/1.44  tff(c_334, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_7')), inference(splitLeft, [status(thm)], [c_203])).
% 2.97/1.44  tff(c_110, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.97/1.44  tff(c_114, plain, (v4_relat_1('#skF_7', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_110])).
% 2.97/1.44  tff(c_141, plain, (![B_91, A_92]: (r1_tarski(k1_relat_1(B_91), A_92) | ~v4_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.97/1.44  tff(c_18, plain, (![B_17, A_16]: (k1_tarski(B_17)=A_16 | k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_tarski(B_17)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.97/1.44  tff(c_626, plain, (![B_145, B_146]: (k1_tarski(B_145)=k1_relat_1(B_146) | k1_relat_1(B_146)=k1_xboole_0 | ~v4_relat_1(B_146, k1_tarski(B_145)) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_141, c_18])).
% 2.97/1.44  tff(c_632, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_7') | k1_relat_1('#skF_7')=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_114, c_626])).
% 2.97/1.44  tff(c_635, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_7') | k1_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_108, c_632])).
% 2.97/1.44  tff(c_636, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_334, c_635])).
% 2.97/1.44  tff(c_52, plain, (![A_42]: (r2_hidden('#skF_3'(A_42), A_42) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.97/1.44  tff(c_267, plain, (![A_113, B_114, C_115]: (r2_hidden('#skF_2'(A_113, B_114, C_115), k1_relat_1(C_115)) | ~r2_hidden(A_113, k9_relat_1(C_115, B_114)) | ~v1_relat_1(C_115))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.97/1.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.44  tff(c_335, plain, (![C_121, A_122, B_123]: (~v1_xboole_0(k1_relat_1(C_121)) | ~r2_hidden(A_122, k9_relat_1(C_121, B_123)) | ~v1_relat_1(C_121))), inference(resolution, [status(thm)], [c_267, c_2])).
% 2.97/1.44  tff(c_359, plain, (![C_121, B_123]: (~v1_xboole_0(k1_relat_1(C_121)) | ~v1_relat_1(C_121) | k9_relat_1(C_121, B_123)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_335])).
% 2.97/1.44  tff(c_640, plain, (![B_123]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_7') | k9_relat_1('#skF_7', B_123)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_636, c_359])).
% 2.97/1.44  tff(c_653, plain, (![B_123]: (k9_relat_1('#skF_7', B_123)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_6, c_640])).
% 2.97/1.44  tff(c_417, plain, (![A_130, B_131, C_132, D_133]: (k7_relset_1(A_130, B_131, C_132, D_133)=k9_relat_1(C_132, D_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.97/1.44  tff(c_420, plain, (![D_133]: (k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', D_133)=k9_relat_1('#skF_7', D_133))), inference(resolution, [status(thm)], [c_58, c_417])).
% 2.97/1.44  tff(c_421, plain, (~r1_tarski(k9_relat_1('#skF_7', '#skF_6'), k1_tarski(k1_funct_1('#skF_7', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_54])).
% 2.97/1.44  tff(c_701, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_7', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_653, c_421])).
% 2.97/1.44  tff(c_706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_701])).
% 2.97/1.44  tff(c_708, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_7')), inference(splitRight, [status(thm)], [c_203])).
% 2.97/1.44  tff(c_711, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_708, c_58])).
% 2.97/1.44  tff(c_753, plain, (![A_151, B_152, C_153, D_154]: (k7_relset_1(A_151, B_152, C_153, D_154)=k9_relat_1(C_153, D_154) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.97/1.44  tff(c_756, plain, (![D_154]: (k7_relset_1(k1_relat_1('#skF_7'), '#skF_5', '#skF_7', D_154)=k9_relat_1('#skF_7', D_154))), inference(resolution, [status(thm)], [c_711, c_753])).
% 2.97/1.44  tff(c_707, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', '#skF_6'), k2_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_203])).
% 2.97/1.44  tff(c_752, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_7'), '#skF_5', '#skF_7', '#skF_6'), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_708, c_707])).
% 2.97/1.44  tff(c_774, plain, (~r1_tarski(k9_relat_1('#skF_7', '#skF_6'), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_756, c_752])).
% 2.97/1.44  tff(c_786, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_774])).
% 2.97/1.44  tff(c_790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_786])).
% 2.97/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.44  
% 2.97/1.44  Inference rules
% 2.97/1.44  ----------------------
% 2.97/1.44  #Ref     : 0
% 2.97/1.44  #Sup     : 152
% 2.97/1.44  #Fact    : 0
% 2.97/1.44  #Define  : 0
% 2.97/1.44  #Split   : 1
% 2.97/1.44  #Chain   : 0
% 2.97/1.44  #Close   : 0
% 2.97/1.44  
% 2.97/1.44  Ordering : KBO
% 2.97/1.44  
% 2.97/1.44  Simplification rules
% 2.97/1.44  ----------------------
% 2.97/1.44  #Subsume      : 34
% 2.97/1.44  #Demod        : 98
% 2.97/1.44  #Tautology    : 73
% 2.97/1.44  #SimpNegUnit  : 2
% 2.97/1.44  #BackRed      : 9
% 2.97/1.44  
% 2.97/1.44  #Partial instantiations: 0
% 2.97/1.44  #Strategies tried      : 1
% 2.97/1.44  
% 2.97/1.44  Timing (in seconds)
% 2.97/1.44  ----------------------
% 2.97/1.44  Preprocessing        : 0.34
% 2.97/1.44  Parsing              : 0.18
% 2.97/1.44  CNF conversion       : 0.02
% 2.97/1.44  Main loop            : 0.31
% 2.97/1.44  Inferencing          : 0.11
% 2.97/1.44  Reduction            : 0.10
% 2.97/1.44  Demodulation         : 0.07
% 2.97/1.44  BG Simplification    : 0.02
% 2.97/1.44  Subsumption          : 0.05
% 2.97/1.44  Abstraction          : 0.01
% 2.97/1.44  MUC search           : 0.00
% 2.97/1.44  Cooper               : 0.00
% 2.97/1.44  Total                : 0.69
% 2.97/1.44  Index Insertion      : 0.00
% 2.97/1.44  Index Deletion       : 0.00
% 2.97/1.44  Index Matching       : 0.00
% 2.97/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
